import subprocess

from prop_lang.variable import Variable


def syfco_ltl(tlsf_file: str) -> str:
    try:
        LTL_cmd = "syfco -f ltl -q double -m fully " + tlsf_file
        so = subprocess.getstatusoutput(LTL_cmd)
        LTL_str: str = so[1]

        return LTL_str
    except Exception as err:
        raise err


def syfco_ltl_in(tlsf_file: str):
    try:
        INS_cmd = "syfco -f ltl --print-input-signals " + tlsf_file
        so = subprocess.getstatusoutput(INS_cmd)
        INS_str: str = so[1]
        INS = [Variable(a.strip(" ")) for a in INS_str.split(",")]

        return INS
    except Exception as err:
        raise err


def syfco_ltl_out(tlsf_file: str):
    try:
        OUTS_cmd = "syfco -f ltl --print-output-signals " + tlsf_file
        so = subprocess.getstatusoutput(OUTS_cmd)
        OUTS_str: str = so[1]
        OUTS = [Variable(a.strip(" ")) for a in OUTS_str.split(",")]

        return OUTS
    except Exception as err:
        raise err
