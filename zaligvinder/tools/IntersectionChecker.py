import subprocess
import tempfile
import os
import shutil
import utils
import sys
import timer

def run (params,eq,timeout,ploc,wd,solver="1",param="60"):
    path = ploc.findProgram ("IntersectionChecker")
    if not path:
        raise "IntersectionChecker Not in Path"
    tempd = tempfile.mkdtemp ()
    txtfile = os.path.join (tempd,"IntersectionChecker_out.txt")
    rawfile = eq.replace(".smt2",".txt")
    # write the content of the rawfile to a txt file
    f=open(rawfile,"r")
    copy=open(txtfile,"w")
    for l in f:
        copy.write(l)
    f.close()
    copy.close()

    time = timer.Timer ()
    try:
        out = subprocess.check_output ([path]+params+[txtfile],timeout=timeout,stderr=subprocess.STDOUT).decode().strip()
    except subprocess.TimeoutExpired:
        return utils.Result(None,timeout*1000,True,1)
    except subprocess.CalledProcessError as e:
        time.stop()

        if time.getTime() >= timeout:
            return utils.Result(None,time.getTime_ms(),True,1)
        else:
            out = "Error in " + eq + ": " + str(e.output)
            return utils.Result(None,time.getTime_ms(),False,1,out)
            """if "SIG" in str(e):          
                return utils.Result(None,time.getTime(),False,1,out)
            else:
                # treat unsupported operations as timeout:
                return utils.Result(None,timeout,True,1,str(e))
            """
    time.stop ()
    shutil.rmtree (tempd)
    if "false" in out:
        return utils.Result(False,time.getTime_ms (),False,1,"unsat")
    elif "true" in out:
        return utils.Result(True,time.getTime_ms (),False,1,"sat","\n".join(out.split("\n")[1:]))
    elif time.getTime() >= timeout:
        return utils.Result(None,time.getTime_ms (),True,1)
    else:
        # must be an error
        return utils.Result(None,time.getTime_ms (), False,1,f"Error in {rawfile} # stdout: {out}")

def addRunner (addto):
    from functools import partial
    params = {
        "CC" : ["CC"],
        "EQ" : ["EQ"],
        "PO" : ["PO"],
        "FO" : ["FO"]
    }

    for i in params.keys():
        addto['IntersectionChecker-'+i] = partial(run,params[i])


if __name__ == "__main__":
    print(run (sys.argv[1],None))