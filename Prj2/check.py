#!/usr/bin/python3
import os
import subprocess
import sys
from os import path
from subprocess import PIPE

ROOT_DIR = path.dirname(path.abspath(__file__))
CONFIG_FILE = "config"
MAX_RUNTIME = 5
DELAY_PENALTY = 0.8
BUILD_DIRNAME = "out"
TESTCASE_DIRNAME = "testcase"
BINARY_NAME = "IRGenerate"
MODE_STRING = "run-ir"


def run_cmd(cmd_str, check=True, timeout=None):
    args = cmd_str.split()
    p = subprocess.run(args, check=check, stdout=PIPE, stderr=PIPE, timeout=timeout)
    return "".join(map(chr, p.stdout))


def build():
    try:
        orig_cwd = os.getcwd()
        os.chdir(ROOT_DIR)
        run_cmd("dotnet build -o %s" % BUILD_DIRNAME)
        os.chdir(orig_cwd)
        return True
    except Exception as e:
        return False


def check(submit_files, point, tc_num, is_delay):
    # If any of the file is missing, it means no submission.
    for submit_file in submit_files:
        src_path = path.join(ROOT_DIR, submit_file)
        if not path.isfile(src_path):  # Not submitted
            return (" ", 0.0)

    # Build the problem directory.
    build_success = build()
    if not build_success:
        return ("C" * tc_num, 0.0)

    # Now start the grading with each testcase file.
    grading_str = ""
    binary = path.join(ROOT_DIR, BUILD_DIRNAME, BINARY_NAME)
    tc_dir = path.join(ROOT_DIR, TESTCASE_DIRNAME)
    for i in range(tc_num):
        ans_path = path.join(tc_dir, "ans-%d" % (i + 1))
        f = open(ans_path)
        ans = f.read()
        f.close()
        prog_path = "%s/prog-%d" % (tc_dir, i + 1)
        input_path = "%s/inp-%d" % (tc_dir, i + 1)
        cmd = "%s %s %s %s" % (binary, MODE_STRING, prog_path, input_path)
        try:
            output = run_cmd(cmd, timeout=MAX_RUNTIME)
            if ans.strip() == output.strip():
                grading_str += "O"
            else:
                grading_str += "X"
        except subprocess.TimeoutExpired:
            grading_str += "T"
        except subprocess.CalledProcessError as e:
            print(e)
            grading_str += "E"

    ratio = float(grading_str.count("O")) / tc_num
    obtained_point = point * ratio
    if is_delay:
        grading_str += " (Delay)"
        obtained_point *= DELAY_PENALTY
    return grading_str, obtained_point


def parse_config():
    f = open(path.join(ROOT_DIR, CONFIG_FILE))
    line = f.readline()
    f.close()
    tokens = line.strip().split()
    problem_name = tokens[0]
    submit_files = tokens[1].split(",")
    point = int(tokens[2])
    tc_num = 13
    return (problem_name, submit_files, point, tc_num)


def main():
    if len(sys.argv) not in [1, 2]:
        # --delay or --normal option is hidden.
        print("Usage: %s" % sys.argv[0])
        exit(1)

    delay_flag = False
    csv_flag = False
    if len(sys.argv) == 2:
        csv_flag = True
        if sys.argv[1] == "--delay":
            delay_flag = True
        elif sys.argv[1] == "--normal":
            pass  # Nothing to do if it's --normal.
        else:
            print("Invalid option: %s" % sys.argv[1])
            exit(1)

    problem_name, submit_files, point, tc_num = parse_config()
    grading_str, obtained_point = check(submit_files, point, tc_num, delay_flag)
    if csv_flag:
        print("%s, %.1f, " % (grading_str, obtained_point), end="")
    else:
        print("[*] Result : %s" % grading_str)


if __name__ == "__main__":
    main()
