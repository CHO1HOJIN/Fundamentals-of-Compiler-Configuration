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
TESTCASE_DIRNAME = "testcase3"
BINARY_NAME = "Optimize"
MODE_STRING = "run-opt"
TC_NUM = 10


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


def parse_output(output):
    result_lines = []
    cost_sum = 0
    for line in output.strip().split("\n"):
        tokens = line.split(",")
        result_lines.append(tokens[0].split(":")[1].strip())
        cost_sum += int(tokens[1].split(":")[1].strip())
    result_str = "\n".join(result_lines).strip()
    return (result_str, cost_sum)


def compute_perf_score(cost, base_cost, opt_cost):
    if cost >= base_cost:
        return 0
    elif cost <= opt_cost:
        return 100
    else:
        return int(100.0 * (base_cost - cost) / (base_cost - opt_cost))


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
    point_per_tc = float(point) / tc_num
    obtained_point = 0
    binary = path.join(ROOT_DIR, BUILD_DIRNAME, BINARY_NAME)
    tc_dir = path.join(ROOT_DIR, TESTCASE_DIRNAME)
    for i in range(tc_num):
        prog_path = path.join(tc_dir, "prog-%d" % (i + 1))
        input_path = path.join(tc_dir, "inp-%d" % (i + 1))
        cost_path = path.join(tc_dir, "cost-%d" % (i + 1))
        ans_path = path.join(tc_dir, "ans-%d" % (i + 1))
        # Read expected answer file
        f = open(ans_path)
        ans = f.read()
        f.close()
        # Read baseline cost information
        f = open(cost_path)
        tokens = f.read().strip().split()
        base_cost, opt_cost = int(tokens[0]), int(tokens[1])
        f.close()
        cmd = "%s %s %s %s" % (binary, MODE_STRING, prog_path, input_path)
        try:
            output = run_cmd(cmd, timeout=MAX_RUNTIME)
            result, cost = parse_output(output)
            perf_score = compute_perf_score(cost, base_cost, opt_cost)
            if ans.strip() == result:
                cmd = "%s %s %s %s" % (binary, "run-ir", prog_path, input_path)
                output = run_cmd(cmd, timeout=MAX_RUNTIME)
                ir_result, ir_cost = parse_output(output)
                grading_str += "O (OPT: %4d | ORIGIN: %4d)\n" % (cost, ir_cost)
                obtained_point += point_per_tc * perf_score / 100
            else:
                result = result.replace("\n", " ")
                ans = ans.replace("\n", " ")
                grading_str += "X (OPT: {result} | ORIGIN: {ans})\n".format(
                    result=result, ans=ans
                )
        except subprocess.TimeoutExpired:
            grading_str += "T (0/100) \n"
        except subprocess.CalledProcessError as e:
            grading_str += "E (0/100) \n"

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
    tc_num = int(tokens[3])
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
    grading_str, obtained_point = check(submit_files, point, TC_NUM, delay_flag)
    if csv_flag:
        print("%s, %.1f, " % (grading_str, obtained_point), end="")
    else:
        print("==========[*] Result==========\n%s" % grading_str)


if __name__ == "__main__":
    main()
