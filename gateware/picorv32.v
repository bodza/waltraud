`default_nettype none
`timescale 1 ns / 1 ps

module picorv32 #(
    parameter        LATCHED_MEM_RDATA = 0,
    parameter        TWO_STAGE_SHIFT = 0,
    parameter        BARREL_SHIFTER = 0,
    parameter        TWO_CYCLE_COMPARE = 0,
    parameter        TWO_CYCLE_ALU = 0,
    parameter        CATCH_MISALIGN = 0,
    parameter        CATCH_ILLINSN = 1,
    parameter        ENABLE_IRQ = 1,
    parameter        ENABLE_IRQ_QREGS = 1,
    parameter        ENABLE_IRQ_TIMER = 0,
    parameter        REGS_INIT_ZERO = 0,
    parameter [31:0] MASKED_IRQ = 32'h 00000000,
    parameter [31:0] LATCHED_IRQ = 32'h ffffffff,
    parameter [31:0] PROGADDR_RESET = 32'h 00000000,
    parameter [31:0] PROGADDR_IRQ = 32'h 00000010,
    parameter [31:0] STACKADDR = 32'h ffffffff
) (
    input clk, resetn,
    output reg trap,

    output reg        mem_valid,
    output reg        mem_instr,
    input             mem_ready,

    output reg [31:0] mem_addr,
    output reg [31:0] mem_wdata,
    output reg [ 3:0] mem_wstrb,
    input      [31:0] mem_rdata,

    // IRQ Interface
    input      [31:0] irq,
    output reg [31:0] eoi
);
    localparam integer irq_timer = 0;
    localparam integer irq_ebreak = 1;
    localparam integer irq_buserror = 2;

    localparam integer irqregs_offset = 32;
    localparam integer regfile_size = 32 + 4 * ENABLE_IRQ * ENABLE_IRQ_QREGS;
    localparam integer regindex_bits = 5 + ENABLE_IRQ * ENABLE_IRQ_QREGS;

    reg [31:0] reg_pc, reg_next_pc, reg_op1, reg_op2, reg_out;
    reg [4:0] reg_sh;

    reg [31:0] next_insn_opcode;

    wire [31:0] next_pc;

    reg irq_delay;
    reg irq_active;
    reg [31:0] irq_mask;
    reg [31:0] irq_pending;
    reg [31:0] timer;

    reg [31:0] cpuregs [0:regfile_size-1];

    integer i;
    initial begin
        if (REGS_INIT_ZERO) begin
            for (i = 0; i < regfile_size; i = i+1)
                cpuregs[i] = 0;
        end
    end

    // Memory Interface

    reg [1:0] mem_state;
    reg [1:0] mem_wordsize;
    reg [31:0] mem_rdata_word;
    reg [31:0] mem_rdata_q;
    reg mem_do_prefetch;
    reg mem_do_rinst;
    reg mem_do_rdata;
    reg mem_do_wdata;

    wire mem_xfer = mem_valid && mem_ready;

    wire mem_done = resetn && ((mem_xfer && |mem_state && (mem_do_rinst || mem_do_rdata || mem_do_wdata)) || (&mem_state && mem_do_rinst));

    wire mem_la_read = resetn && (!mem_state && (mem_do_rinst || mem_do_prefetch || mem_do_rdata));
    wire mem_la_write = resetn && !mem_state && mem_do_wdata;
    wire [31:0] mem_la_addr = (mem_do_prefetch || mem_do_rinst) ? {next_pc[31:2], 2'b00} : {reg_op1[31:2], 2'b00};

    reg [31:0] mem_la_wdata;
    reg [3:0] mem_la_wstrb;

    wire [31:0] mem_rdata_latched = (mem_xfer || LATCHED_MEM_RDATA) ? mem_rdata : mem_rdata_q;

    always @* begin
        (* full_case *)
        case (mem_wordsize)
            0: begin
                mem_la_wdata = reg_op2;
                mem_la_wstrb = 4'b1111;
                mem_rdata_word = mem_rdata;
            end
            1: begin
                mem_la_wdata = {2{reg_op2[15:0]}};
                mem_la_wstrb = reg_op1[1] ? 4'b1100 : 4'b0011;
                case (reg_op1[1])
                    1'b0: mem_rdata_word = {16'b0, mem_rdata[15: 0]};
                    1'b1: mem_rdata_word = {16'b0, mem_rdata[31:16]};
                endcase
            end
            2: begin
                mem_la_wdata = {4{reg_op2[7:0]}};
                mem_la_wstrb = 4'b0001 << reg_op1[1:0];
                case (reg_op1[1:0])
                    2'b00: mem_rdata_word = {24'b0, mem_rdata[ 7: 0]};
                    2'b01: mem_rdata_word = {24'b0, mem_rdata[15: 8]};
                    2'b10: mem_rdata_word = {24'b0, mem_rdata[23:16]};
                    2'b11: mem_rdata_word = {24'b0, mem_rdata[31:24]};
                endcase
            end
        endcase
    end

    always @(posedge clk) begin
        if (mem_xfer) begin
            mem_rdata_q <= mem_rdata;
            next_insn_opcode <= mem_rdata;
        end
    end

    always @(posedge clk) begin
        if (!resetn || trap) begin
            if (!resetn)
                mem_state <= 0;
            if (!resetn || mem_ready)
                mem_valid <= 0;
        end else begin
            if (mem_la_read || mem_la_write) begin
                mem_addr <= mem_la_addr;
                mem_wstrb <= mem_la_wstrb & {4{mem_la_write}};
            end
            if (mem_la_write) begin
                mem_wdata <= mem_la_wdata;
            end
            case (mem_state)
                0: begin
                    if (mem_do_prefetch || mem_do_rinst || mem_do_rdata) begin
                        mem_valid <= 1;
                        mem_instr <= mem_do_prefetch || mem_do_rinst;
                        mem_wstrb <= 0;
                        mem_state <= 1;
                    end
                    if (mem_do_wdata) begin
                        mem_valid <= 1;
                        mem_instr <= 0;
                        mem_state <= 2;
                    end
                end
                1: begin
                    if (mem_xfer) begin
                        mem_valid <= 0;
                        mem_state <= mem_do_rinst || mem_do_rdata ? 0 : 3;
                    end
                end
                2: begin
                    if (mem_xfer) begin
                        mem_valid <= 0;
                        mem_state <= 0;
                    end
                end
                3: begin
                    if (mem_do_rinst) begin
                        mem_state <= 0;
                    end
                end
            endcase
        end
    end

    // Instruction Decoder

    reg instr_lui, instr_auipc, instr_jal, instr_jalr;
    reg instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu;
    reg instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw;
    reg instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai;
    reg instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and;
    reg instr_ecall_ebreak;
    reg instr_getq, instr_setq, instr_retirq, instr_maskirq, instr_waitirq, instr_timer;

    wire instr_trap = CATCH_ILLINSN && !{instr_lui, instr_auipc, instr_jal, instr_jalr,
            instr_beq, instr_bne, instr_blt, instr_bge, instr_bltu, instr_bgeu,
            instr_lb, instr_lh, instr_lw, instr_lbu, instr_lhu, instr_sb, instr_sh, instr_sw,
            instr_addi, instr_slti, instr_sltiu, instr_xori, instr_ori, instr_andi, instr_slli, instr_srli, instr_srai,
            instr_add, instr_sub, instr_sll, instr_slt, instr_sltu, instr_xor, instr_srl, instr_sra, instr_or, instr_and,
            instr_getq, instr_setq, instr_retirq, instr_maskirq, instr_waitirq, instr_timer};

    reg [regindex_bits-1:0] decoded_rd, decoded_rs1, decoded_rs2;
    reg [31:0] decoded_imm, decoded_imm_j;
    reg decoder_trigger;
    reg decoder_trigger_q;
    reg decoder_pseudo_trigger;
    reg decoder_pseudo_trigger_q;

    reg is_lui_auipc_jal;
    reg is_lb_lh_lw_lbu_lhu;
    reg is_slli_srli_srai;
    reg is_jalr_addi_slti_sltiu_xori_ori_andi;
    reg is_sb_sh_sw;
    reg is_sll_srl_sra;
    reg is_lui_auipc_jal_jalr_addi_add_sub;
    reg is_slti_blt_slt;
    reg is_sltiu_bltu_sltu;
    reg is_beq_bne_blt_bge_bltu_bgeu;
    reg is_lbu_lhu_lw;
    reg is_alu_reg_imm;
    reg is_alu_reg_reg;
    reg is_compare;

    always @(posedge clk) begin
        is_lui_auipc_jal <= |{instr_lui, instr_auipc, instr_jal};
        is_lui_auipc_jal_jalr_addi_add_sub <= |{instr_lui, instr_auipc, instr_jal, instr_jalr, instr_addi, instr_add, instr_sub};
        is_slti_blt_slt <= |{instr_slti, instr_blt, instr_slt};
        is_sltiu_bltu_sltu <= |{instr_sltiu, instr_bltu, instr_sltu};
        is_lbu_lhu_lw <= |{instr_lbu, instr_lhu, instr_lw};
        is_compare <= |{is_beq_bne_blt_bge_bltu_bgeu, instr_slti, instr_slt, instr_sltiu, instr_sltu};

        if (mem_do_rinst && mem_done) begin
            instr_lui     <= mem_rdata_latched[6:0] == 7'b0110111;
            instr_auipc   <= mem_rdata_latched[6:0] == 7'b0010111;
            instr_jal     <= mem_rdata_latched[6:0] == 7'b1101111;
            instr_jalr    <= mem_rdata_latched[6:0] == 7'b1100111 && mem_rdata_latched[14:12] == 3'b000;
            instr_retirq  <= mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000010 && ENABLE_IRQ;
            instr_waitirq <= mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000100 && ENABLE_IRQ;

            is_beq_bne_blt_bge_bltu_bgeu <= mem_rdata_latched[6:0] == 7'b1100011;
            is_lb_lh_lw_lbu_lhu          <= mem_rdata_latched[6:0] == 7'b0000011;
            is_sb_sh_sw                  <= mem_rdata_latched[6:0] == 7'b0100011;
            is_alu_reg_imm               <= mem_rdata_latched[6:0] == 7'b0010011;
            is_alu_reg_reg               <= mem_rdata_latched[6:0] == 7'b0110011;

            { decoded_imm_j[31:20], decoded_imm_j[10:1], decoded_imm_j[11], decoded_imm_j[19:12], decoded_imm_j[0] } <= $signed({mem_rdata_latched[31:12], 1'b0});

            decoded_rd <= mem_rdata_latched[11:7];
            decoded_rs1 <= mem_rdata_latched[19:15];
            decoded_rs2 <= mem_rdata_latched[24:20];

            if (mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000000 && ENABLE_IRQ && ENABLE_IRQ_QREGS)
                decoded_rs1[regindex_bits-1] <= 1; // instr_getq

            if (mem_rdata_latched[6:0] == 7'b0001011 && mem_rdata_latched[31:25] == 7'b0000010 && ENABLE_IRQ)
                decoded_rs1 <= ENABLE_IRQ_QREGS ? irqregs_offset : 3; // instr_retirq
        end

        if (decoder_trigger && !decoder_pseudo_trigger) begin
            instr_beq   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b000;
            instr_bne   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b001;
            instr_blt   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b100;
            instr_bge   <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b101;
            instr_bltu  <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b110;
            instr_bgeu  <= is_beq_bne_blt_bge_bltu_bgeu && mem_rdata_q[14:12] == 3'b111;

            instr_lb    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b000;
            instr_lh    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b001;
            instr_lw    <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b010;
            instr_lbu   <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b100;
            instr_lhu   <= is_lb_lh_lw_lbu_lhu && mem_rdata_q[14:12] == 3'b101;

            instr_sb    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b000;
            instr_sh    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b001;
            instr_sw    <= is_sb_sh_sw && mem_rdata_q[14:12] == 3'b010;

            instr_addi  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b000;
            instr_slti  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b010;
            instr_sltiu <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b011;
            instr_xori  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b100;
            instr_ori   <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b110;
            instr_andi  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b111;

            instr_slli  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000;
            instr_srli  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000;
            instr_srai  <= is_alu_reg_imm && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000;

            instr_add   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b000 && mem_rdata_q[31:25] == 7'b0000000;
            instr_sub   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b000 && mem_rdata_q[31:25] == 7'b0100000;
            instr_sll   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000;
            instr_slt   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b010 && mem_rdata_q[31:25] == 7'b0000000;
            instr_sltu  <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b011 && mem_rdata_q[31:25] == 7'b0000000;
            instr_xor   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b100 && mem_rdata_q[31:25] == 7'b0000000;
            instr_srl   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000;
            instr_sra   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000;
            instr_or    <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b110 && mem_rdata_q[31:25] == 7'b0000000;
            instr_and   <= is_alu_reg_reg && mem_rdata_q[14:12] == 3'b111 && mem_rdata_q[31:25] == 7'b0000000;

            instr_ecall_ebreak <= (mem_rdata_q[6:0] == 7'b1110011 && !mem_rdata_q[31:21] && !mem_rdata_q[19:7]);

            instr_getq    <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000000 && ENABLE_IRQ && ENABLE_IRQ_QREGS;
            instr_setq    <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000001 && ENABLE_IRQ && ENABLE_IRQ_QREGS;
            instr_maskirq <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000011 && ENABLE_IRQ;
            instr_timer   <= mem_rdata_q[6:0] == 7'b0001011 && mem_rdata_q[31:25] == 7'b0000101 && ENABLE_IRQ && ENABLE_IRQ_TIMER;

            is_slli_srli_srai <= is_alu_reg_imm && |{
                mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000,
                mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000,
                mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000
            };

            is_jalr_addi_slti_sltiu_xori_ori_andi <= instr_jalr || is_alu_reg_imm && |{
                mem_rdata_q[14:12] == 3'b000,
                mem_rdata_q[14:12] == 3'b010,
                mem_rdata_q[14:12] == 3'b011,
                mem_rdata_q[14:12] == 3'b100,
                mem_rdata_q[14:12] == 3'b110,
                mem_rdata_q[14:12] == 3'b111
            };

            is_sll_srl_sra <= is_alu_reg_reg && |{
                mem_rdata_q[14:12] == 3'b001 && mem_rdata_q[31:25] == 7'b0000000,
                mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0000000,
                mem_rdata_q[14:12] == 3'b101 && mem_rdata_q[31:25] == 7'b0100000
            };

            is_lui_auipc_jal_jalr_addi_add_sub <= 0;
            is_compare <= 0;

            (* parallel_case *)
            case (1'b1)
                instr_jal:
                    decoded_imm <= decoded_imm_j;
                |{instr_lui, instr_auipc}:
                    decoded_imm <= mem_rdata_q[31:12] << 12;
                |{instr_jalr, is_lb_lh_lw_lbu_lhu, is_alu_reg_imm}:
                    decoded_imm <= $signed(mem_rdata_q[31:20]);
                is_beq_bne_blt_bge_bltu_bgeu:
                    decoded_imm <= $signed({mem_rdata_q[31], mem_rdata_q[7], mem_rdata_q[30:25], mem_rdata_q[11:8], 1'b0});
                is_sb_sh_sw:
                    decoded_imm <= $signed({mem_rdata_q[31:25], mem_rdata_q[11:7]});
                default:
                    decoded_imm <= 1'bx;
            endcase
        end

        if (!resetn) begin
            is_beq_bne_blt_bge_bltu_bgeu <= 0;
            is_compare <= 0;

            instr_beq   <= 0;
            instr_bne   <= 0;
            instr_blt   <= 0;
            instr_bge   <= 0;
            instr_bltu  <= 0;
            instr_bgeu  <= 0;

            instr_addi  <= 0;
            instr_slti  <= 0;
            instr_sltiu <= 0;
            instr_xori  <= 0;
            instr_ori   <= 0;
            instr_andi  <= 0;

            instr_add   <= 0;
            instr_sub   <= 0;
            instr_sll   <= 0;
            instr_slt   <= 0;
            instr_sltu  <= 0;
            instr_xor   <= 0;
            instr_srl   <= 0;
            instr_sra   <= 0;
            instr_or    <= 0;
            instr_and   <= 0;
        end
    end

    // Main State Machine

    localparam cpu_state_trap   = 8'b10000000;
    localparam cpu_state_fetch  = 8'b01000000;
    localparam cpu_state_ld_rs1 = 8'b00100000;
    localparam cpu_state_ld_rs2 = 8'b00010000;
    localparam cpu_state_exec   = 8'b00001000;
    localparam cpu_state_shift  = 8'b00000100;
    localparam cpu_state_stmem  = 8'b00000010;
    localparam cpu_state_ldmem  = 8'b00000001;

    reg [7:0] cpu_state;
    reg [1:0] irq_state;

    reg set_mem_do_rinst;
    reg set_mem_do_rdata;
    reg set_mem_do_wdata;

    reg latched_store;
    reg latched_stalu;
    reg latched_branch;
    reg latched_is_lu;
    reg latched_is_lh;
    reg latched_is_lb;
    reg [regindex_bits-1:0] latched_rd;

    reg [31:0] current_pc;
    assign next_pc = latched_store && latched_branch ? reg_out & ~1 : reg_next_pc;

    reg [31:0] next_irq_pending;
    reg do_waitirq;

    reg [31:0] alu_out, alu_out_q;
    reg alu_out_0, alu_out_0_q;
    reg alu_wait, alu_wait_2;

    reg [31:0] alu_add_sub;
    reg [31:0] alu_shl, alu_shr;
    reg alu_eq, alu_ltu, alu_lts;

    generate if (TWO_CYCLE_ALU) begin
        always @(posedge clk) begin
            alu_add_sub <= instr_sub ? reg_op1 - reg_op2 : reg_op1 + reg_op2;
            alu_eq <= reg_op1 == reg_op2;
            alu_lts <= $signed(reg_op1) < $signed(reg_op2);
            alu_ltu <= reg_op1 < reg_op2;
            alu_shl <= reg_op1 << reg_op2[4:0];
            alu_shr <= $signed({instr_sra || instr_srai ? reg_op1[31] : 1'b0, reg_op1}) >>> reg_op2[4:0];
        end
    end else begin
        always @* begin
            alu_add_sub = instr_sub ? reg_op1 - reg_op2 : reg_op1 + reg_op2;
            alu_eq = reg_op1 == reg_op2;
            alu_lts = $signed(reg_op1) < $signed(reg_op2);
            alu_ltu = reg_op1 < reg_op2;
            alu_shl = reg_op1 << reg_op2[4:0];
            alu_shr = $signed({instr_sra || instr_srai ? reg_op1[31] : 1'b0, reg_op1}) >>> reg_op2[4:0];
        end
    end endgenerate

    always @* begin
        alu_out_0 = 'bx;
        (* parallel_case, full_case *)
        case (1'b1)
            instr_beq:
                alu_out_0 = alu_eq;
            instr_bne:
                alu_out_0 = !alu_eq;
            instr_bge:
                alu_out_0 = !alu_lts;
            instr_bgeu:
                alu_out_0 = !alu_ltu;
            is_slti_blt_slt && (!TWO_CYCLE_COMPARE || !{instr_beq, instr_bne, instr_bge, instr_bgeu}):
                alu_out_0 = alu_lts;
            is_sltiu_bltu_sltu && (!TWO_CYCLE_COMPARE || !{instr_beq, instr_bne, instr_bge, instr_bgeu}):
                alu_out_0 = alu_ltu;
        endcase

        alu_out = 'bx;
        (* parallel_case, full_case *)
        case (1'b1)
            is_lui_auipc_jal_jalr_addi_add_sub:
                alu_out = alu_add_sub;
            is_compare:
                alu_out = alu_out_0;
            instr_xori || instr_xor:
                alu_out = reg_op1 ^ reg_op2;
            instr_ori || instr_or:
                alu_out = reg_op1 | reg_op2;
            instr_andi || instr_and:
                alu_out = reg_op1 & reg_op2;
            BARREL_SHIFTER && (instr_sll || instr_slli):
                alu_out = alu_shl;
            BARREL_SHIFTER && (instr_srl || instr_srli || instr_sra || instr_srai):
                alu_out = alu_shr;
        endcase
    end

    reg cpuregs_write;
    reg [31:0] cpuregs_wrdata;
    reg [31:0] cpuregs_rs1;
    reg [31:0] cpuregs_rs2;

    always @* begin
        cpuregs_write = 0;
        cpuregs_wrdata = 'bx;

        if (cpu_state == cpu_state_fetch) begin
            (* parallel_case *)
            case (1'b1)
                latched_branch: begin
                    cpuregs_wrdata = reg_pc + 4;
                    cpuregs_write = 1;
                end
                latched_store && !latched_branch: begin
                    cpuregs_wrdata = latched_stalu ? alu_out_q : reg_out;
                    cpuregs_write = 1;
                end
                ENABLE_IRQ && irq_state[0]: begin
                    cpuregs_wrdata = reg_next_pc;
                    cpuregs_write = 1;
                end
                ENABLE_IRQ && irq_state[1]: begin
                    cpuregs_wrdata = irq_pending & ~irq_mask;
                    cpuregs_write = 1;
                end
            endcase
        end
    end

    always @(posedge clk) begin
        if (resetn && cpuregs_write && latched_rd)
            cpuregs[latched_rd] <= cpuregs_wrdata;
    end

    always @* begin
        cpuregs_rs1 = decoded_rs1 ? cpuregs[decoded_rs1] : 0;
        cpuregs_rs2 = decoded_rs2 ? cpuregs[decoded_rs2] : 0;
    end

    always @(posedge clk) begin
        trap <= 0;
        reg_sh <= 'bx;
        reg_out <= 'bx;
        set_mem_do_rinst = 0;
        set_mem_do_rdata = 0;
        set_mem_do_wdata = 0;

        alu_out_0_q <= alu_out_0;
        alu_out_q <= alu_out;

        alu_wait <= 0;
        alu_wait_2 <= 0;

        next_irq_pending = ENABLE_IRQ ? irq_pending & LATCHED_IRQ : 'bx;

        if (ENABLE_IRQ && ENABLE_IRQ_TIMER && timer) begin
            timer <= timer - 1;
        end

        decoder_trigger <= mem_do_rinst && mem_done;
        decoder_trigger_q <= decoder_trigger;
        decoder_pseudo_trigger <= 0;
        decoder_pseudo_trigger_q <= decoder_pseudo_trigger;
        do_waitirq <= 0;

        if (!resetn) begin
            reg_pc <= PROGADDR_RESET;
            reg_next_pc <= PROGADDR_RESET;
            latched_store <= 0;
            latched_stalu <= 0;
            latched_branch <= 0;
            latched_is_lu <= 0;
            latched_is_lh <= 0;
            latched_is_lb <= 0;
            irq_active <= 0;
            irq_delay <= 0;
            irq_mask <= ~0;
            next_irq_pending = 0;
            irq_state <= 0;
            eoi <= 0;
            timer <= 0;
            if (~STACKADDR) begin
                latched_store <= 1;
                latched_rd <= 2;
                reg_out <= STACKADDR;
            end
            cpu_state <= cpu_state_fetch;
        end else
        (* parallel_case, full_case *)
        case (cpu_state)
            cpu_state_trap: begin
                trap <= 1;
            end

            cpu_state_fetch: begin
                mem_do_rinst <= !decoder_trigger && !do_waitirq;
                mem_wordsize <= 0;

                current_pc = reg_next_pc;

                (* parallel_case *)
                case (1'b1)
                    latched_branch: begin
                        current_pc = latched_store ? (latched_stalu ? alu_out_q : reg_out) & ~1 : reg_next_pc;
                    end
                    ENABLE_IRQ && irq_state[0]: begin
                        current_pc = PROGADDR_IRQ;
                        irq_active <= 1;
                        mem_do_rinst <= 1;
                    end
                    ENABLE_IRQ && irq_state[1]: begin
                        eoi <= irq_pending & ~irq_mask;
                        next_irq_pending = next_irq_pending & irq_mask;
                    end
                endcase

                reg_pc <= current_pc;
                reg_next_pc <= current_pc;

                latched_store <= 0;
                latched_stalu <= 0;
                latched_branch <= 0;
                latched_is_lu <= 0;
                latched_is_lh <= 0;
                latched_is_lb <= 0;
                latched_rd <= decoded_rd;

                if (ENABLE_IRQ && ((decoder_trigger && !irq_active && !irq_delay && |(irq_pending & ~irq_mask)) || irq_state)) begin
                    irq_state <=
                        irq_state == 2'b00 ? 2'b01 :
                        irq_state == 2'b01 ? 2'b10 : 2'b00;
                    if (ENABLE_IRQ_QREGS)
                        latched_rd <= irqregs_offset | irq_state[0];
                    else
                        latched_rd <= irq_state[0] ? 4 : 3;
                end else
                if (ENABLE_IRQ && (decoder_trigger || do_waitirq) && instr_waitirq) begin
                    if (irq_pending) begin
                        latched_store <= 1;
                        reg_out <= irq_pending;
                        reg_next_pc <= current_pc + 4;
                        mem_do_rinst <= 1;
                    end else
                        do_waitirq <= 1;
                end else
                if (decoder_trigger) begin
                    irq_delay <= irq_active;
                    reg_next_pc <= current_pc + 4;
                    if (instr_jal) begin
                        mem_do_rinst <= 1;
                        reg_next_pc <= current_pc + decoded_imm_j;
                        latched_branch <= 1;
                    end else begin
                        mem_do_rinst <= 0;
                        mem_do_prefetch <= !instr_jalr && !instr_retirq;
                        cpu_state <= cpu_state_ld_rs1;
                    end
                end
            end

            cpu_state_ld_rs1: begin
                reg_op1 <= 'bx;
                reg_op2 <= 'bx;

                (* parallel_case *)
                case (1'b1)
                    CATCH_ILLINSN && instr_trap: begin
                        if (ENABLE_IRQ && !irq_mask[irq_ebreak] && !irq_active) begin
                            next_irq_pending[irq_ebreak] = 1;
                            cpu_state <= cpu_state_fetch;
                        end else
                            cpu_state <= cpu_state_trap;
                    end
                    is_lui_auipc_jal: begin
                        reg_op1 <= instr_lui ? 0 : reg_pc;
                        reg_op2 <= decoded_imm;
                        if (TWO_CYCLE_ALU)
                            alu_wait <= 1;
                        else
                            mem_do_rinst <= mem_do_prefetch;
                        cpu_state <= cpu_state_exec;
                    end
                    ENABLE_IRQ && ENABLE_IRQ_QREGS && instr_getq: begin
                        reg_out <= cpuregs_rs1;
                        latched_store <= 1;
                        cpu_state <= cpu_state_fetch;
                    end
                    ENABLE_IRQ && ENABLE_IRQ_QREGS && instr_setq: begin
                        reg_out <= cpuregs_rs1;
                        latched_rd <= latched_rd | irqregs_offset;
                        latched_store <= 1;
                        cpu_state <= cpu_state_fetch;
                    end
                    ENABLE_IRQ && instr_retirq: begin
                        eoi <= 0;
                        irq_active <= 0;
                        latched_branch <= 1;
                        latched_store <= 1;
                        reg_out <= CATCH_MISALIGN ? (cpuregs_rs1 & 32'h fffffffe) : cpuregs_rs1;
                        cpu_state <= cpu_state_fetch;
                    end
                    ENABLE_IRQ && instr_maskirq: begin
                        latched_store <= 1;
                        reg_out <= irq_mask;
                        irq_mask <= cpuregs_rs1 | MASKED_IRQ;
                        cpu_state <= cpu_state_fetch;
                    end
                    ENABLE_IRQ && ENABLE_IRQ_TIMER && instr_timer: begin
                        latched_store <= 1;
                        reg_out <= timer;
                        timer <= cpuregs_rs1;
                        cpu_state <= cpu_state_fetch;
                    end
                    is_lb_lh_lw_lbu_lhu && !instr_trap: begin
                        reg_op1 <= cpuregs_rs1;
                        cpu_state <= cpu_state_ldmem;
                        mem_do_rinst <= 1;
                    end
                    is_slli_srli_srai && !BARREL_SHIFTER: begin
                        reg_op1 <= cpuregs_rs1;
                        reg_sh <= decoded_rs2;
                        cpu_state <= cpu_state_shift;
                    end
                    is_jalr_addi_slti_sltiu_xori_ori_andi, is_slli_srli_srai && BARREL_SHIFTER: begin
                        reg_op1 <= cpuregs_rs1;
                        reg_op2 <= is_slli_srli_srai && BARREL_SHIFTER ? decoded_rs2 : decoded_imm;
                        if (TWO_CYCLE_ALU)
                            alu_wait <= 1;
                        else
                            mem_do_rinst <= mem_do_prefetch;
                        cpu_state <= cpu_state_exec;
                    end
                    default: begin
                        reg_op1 <= cpuregs_rs1;
                        reg_sh <= cpuregs_rs2;
                        reg_op2 <= cpuregs_rs2;
                        (* parallel_case *)
                        case (1'b1)
                            is_sb_sh_sw: begin
                                cpu_state <= cpu_state_stmem;
                                mem_do_rinst <= 1;
                            end
                            is_sll_srl_sra && !BARREL_SHIFTER: begin
                                cpu_state <= cpu_state_shift;
                            end
                            default: begin
                                if (TWO_CYCLE_ALU || (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu)) begin
                                    alu_wait_2 <= TWO_CYCLE_ALU && (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu);
                                    alu_wait <= 1;
                                end else
                                    mem_do_rinst <= mem_do_prefetch;
                                cpu_state <= cpu_state_exec;
                            end
                        endcase
                    end
                endcase
            end

            cpu_state_ld_rs2: begin
                reg_sh <= cpuregs_rs2;
                reg_op2 <= cpuregs_rs2;

                (* parallel_case *)
                case (1'b1)
                    is_sb_sh_sw: begin
                        cpu_state <= cpu_state_stmem;
                        mem_do_rinst <= 1;
                    end
                    is_sll_srl_sra && !BARREL_SHIFTER: begin
                        cpu_state <= cpu_state_shift;
                    end
                    default: begin
                        if (TWO_CYCLE_ALU || (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu)) begin
                            alu_wait_2 <= TWO_CYCLE_ALU && (TWO_CYCLE_COMPARE && is_beq_bne_blt_bge_bltu_bgeu);
                            alu_wait <= 1;
                        end else
                            mem_do_rinst <= mem_do_prefetch;
                        cpu_state <= cpu_state_exec;
                    end
                endcase
            end

            cpu_state_exec: begin
                reg_out <= reg_pc + decoded_imm;
                if ((TWO_CYCLE_ALU || TWO_CYCLE_COMPARE) && (alu_wait || alu_wait_2)) begin
                    mem_do_rinst <= mem_do_prefetch && !alu_wait_2;
                    alu_wait <= alu_wait_2;
                end else
                if (is_beq_bne_blt_bge_bltu_bgeu) begin
                    latched_rd <= 0;
                    latched_store <= TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0;
                    latched_branch <= TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0;
                    if (mem_done)
                        cpu_state <= cpu_state_fetch;
                    if (TWO_CYCLE_COMPARE ? alu_out_0_q : alu_out_0) begin
                        decoder_trigger <= 0;
                        set_mem_do_rinst = 1;
                    end
                end else begin
                    latched_branch <= instr_jalr;
                    latched_store <= 1;
                    latched_stalu <= 1;
                    cpu_state <= cpu_state_fetch;
                end
            end

            cpu_state_shift: begin
                latched_store <= 1;
                if (reg_sh == 0) begin
                    reg_out <= reg_op1;
                    mem_do_rinst <= mem_do_prefetch;
                    cpu_state <= cpu_state_fetch;
                end else if (TWO_STAGE_SHIFT && reg_sh >= 4) begin
                    (* parallel_case, full_case *)
                    case (1'b1)
                        instr_slli || instr_sll: reg_op1 <= reg_op1 << 4;
                        instr_srli || instr_srl: reg_op1 <= reg_op1 >> 4;
                        instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 4;
                    endcase
                    reg_sh <= reg_sh - 4;
                end else begin
                    (* parallel_case, full_case *)
                    case (1'b1)
                        instr_slli || instr_sll: reg_op1 <= reg_op1 << 1;
                        instr_srli || instr_srl: reg_op1 <= reg_op1 >> 1;
                        instr_srai || instr_sra: reg_op1 <= $signed(reg_op1) >>> 1;
                    endcase
                    reg_sh <= reg_sh - 1;
                end
            end

            cpu_state_stmem: begin
                if (!mem_do_prefetch || mem_done) begin
                    if (!mem_do_wdata) begin
                        (* parallel_case, full_case *)
                        case (1'b1)
                            instr_sb: mem_wordsize <= 2;
                            instr_sh: mem_wordsize <= 1;
                            instr_sw: mem_wordsize <= 0;
                        endcase
                        reg_op1 <= reg_op1 + decoded_imm;
                        set_mem_do_wdata = 1;
                    end
                    if (!mem_do_prefetch && mem_done) begin
                        cpu_state <= cpu_state_fetch;
                        decoder_trigger <= 1;
                        decoder_pseudo_trigger <= 1;
                    end
                end
            end

            cpu_state_ldmem: begin
                latched_store <= 1;
                if (!mem_do_prefetch || mem_done) begin
                    if (!mem_do_rdata) begin
                        (* parallel_case, full_case *)
                        case (1'b1)
                            instr_lb || instr_lbu: mem_wordsize <= 2;
                            instr_lh || instr_lhu: mem_wordsize <= 1;
                            instr_lw: mem_wordsize <= 0;
                        endcase
                        latched_is_lu <= is_lbu_lhu_lw;
                        latched_is_lh <= instr_lh;
                        latched_is_lb <= instr_lb;
                        reg_op1 <= reg_op1 + decoded_imm;
                        set_mem_do_rdata = 1;
                    end
                    if (!mem_do_prefetch && mem_done) begin
                        (* parallel_case, full_case *)
                        case (1'b1)
                            latched_is_lu: reg_out <= mem_rdata_word;
                            latched_is_lh: reg_out <= $signed(mem_rdata_word[15:0]);
                            latched_is_lb: reg_out <= $signed(mem_rdata_word[7:0]);
                        endcase
                        decoder_trigger <= 1;
                        decoder_pseudo_trigger <= 1;
                        cpu_state <= cpu_state_fetch;
                    end
                end
            end
        endcase

        if (ENABLE_IRQ) begin
            next_irq_pending = next_irq_pending | irq;
            if (ENABLE_IRQ_TIMER && timer)
                if (timer - 1 == 0)
                    next_irq_pending[irq_timer] = 1;
        end

        if (CATCH_MISALIGN && resetn && (mem_do_rdata || mem_do_wdata)) begin
            if (mem_wordsize == 0 && reg_op1[1:0] != 0) begin
                if (ENABLE_IRQ && !irq_mask[irq_buserror] && !irq_active) begin
                    next_irq_pending[irq_buserror] = 1;
                end else
                    cpu_state <= cpu_state_trap;
            end
            if (mem_wordsize == 1 && reg_op1[0] != 0) begin
                if (ENABLE_IRQ && !irq_mask[irq_buserror] && !irq_active) begin
                    next_irq_pending[irq_buserror] = 1;
                end else
                    cpu_state <= cpu_state_trap;
            end
        end
        if (CATCH_MISALIGN && resetn && mem_do_rinst && |reg_pc[1:0]) begin
            if (ENABLE_IRQ && !irq_mask[irq_buserror] && !irq_active) begin
                next_irq_pending[irq_buserror] = 1;
            end else
                cpu_state <= cpu_state_trap;
        end
        if (!CATCH_ILLINSN && decoder_trigger_q && !decoder_pseudo_trigger_q && instr_ecall_ebreak) begin
            cpu_state <= cpu_state_trap;
        end

        if (!resetn || mem_done) begin
            mem_do_prefetch <= 0;
            mem_do_rinst <= 0;
            mem_do_rdata <= 0;
            mem_do_wdata <= 0;
        end

        if (set_mem_do_rinst)
            mem_do_rinst <= 1;
        if (set_mem_do_rdata)
            mem_do_rdata <= 1;
        if (set_mem_do_wdata)
            mem_do_wdata <= 1;

        irq_pending <= next_irq_pending & ~MASKED_IRQ;

        if (!CATCH_MISALIGN) begin
            reg_pc[1:0] <= 0;
            reg_next_pc[1:0] <= 0;
        end
        current_pc = 'bx;
    end
endmodule
