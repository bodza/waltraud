#!/usr/bin/env python3

import argparse, os, serial, signal, sys, termios, threading, time

class Console:
    def __init__(self):
        self.fd = sys.stdin.fileno()
        self.default_settings = termios.tcgetattr(self.fd)

    def configure(self):
        settings = termios.tcgetattr(self.fd)
        settings[3] = settings[3] & ~termios.ICANON & ~termios.ECHO
        settings[6][termios.VMIN] = 1
        settings[6][termios.VTIME] = 0
        termios.tcsetattr(self.fd, termios.TCSANOW, settings)

    def unconfigure(self):
        termios.tcsetattr(self.fd, termios.TCSAFLUSH, self.default_settings)

    def getkey(self):
        return os.read(self.fd, 1)

class Term:
    def __init__(self):
        self.reader_alive = False
        self.writer_alive = False

        self.console = Console()

        signal.signal(signal.SIGINT, self.sigint)
        self.sigint_time_last = 0

    def open(self, port, baudrate):
        if hasattr(self, "port"):
            return
        self.port = serial.serial_for_url(port, baudrate)

    def close(self):
        if not hasattr(self, "port"):
            return
        self.port.close()
        del self.port

    def sigint(self, sig, frame):
        self.port.write(b"\x03")
        sigint_time_current = time.time()
        # Exit term if 2 CTRL-C pressed in less than 0.5s.
        if (sigint_time_current - self.sigint_time_last < 0.5):
            self.console.unconfigure()
            self.close()
            sys.exit()
        else:
            self.sigint_time_last = sigint_time_current

    def reader(self):
        try:
            while self.reader_alive:
                c = self.port.read()
                sys.stdout.buffer.write(c)
                sys.stdout.flush()
        except serial.SerialException:
            self.reader_alive = False
            self.console.unconfigure()
            raise

    def start_reader(self):
        self.reader_alive = True
        self.reader_thread = threading.Thread(target=self.reader)
        self.reader_thread.setDaemon(True)
        self.reader_thread.start()

    def stop_reader(self):
        self.reader_alive = False
        self.reader_thread.join()

    def writer(self):
        try:
            while self.writer_alive:
                b = self.console.getkey()
                if b == b"\x03":
                    self.stop()
                elif b == b"\n":
                    self.port.write(b"\x0a")
                else:
                    self.port.write(b)
        except:
            self.writer_alive = False
            self.console.unconfigure()
            raise

    def start_writer(self):
        self.writer_alive = True
        self.writer_thread = threading.Thread(target=self.writer)
        self.writer_thread.setDaemon(True)
        self.writer_thread.start()

    def stop_writer(self):
        self.writer_alive = False
        self.writer_thread.join()

    def start(self):
        self.start_reader()
        self.start_writer()

    def stop(self):
        self.reader_alive = False
        self.writer_alive = False

    def join(self, writer_only=False):
        self.writer_thread.join()
        if not writer_only:
            self.reader_thread.join()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("port", help="serial port")
    parser.add_argument("--baud", default=115200, help="serial baudrate")
    args = parser.parse_args()

    term = Term()
    term.open(args.port, int(float(args.baud)))
    term.console.configure()
    term.start()
    term.join(True)

if __name__ == "__main__":
    main()
