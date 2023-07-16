#!/usr/bin/python

from runners.multi import TheRunner as testrunner
import utils
import storage
import voting.majority as voting

import models.RegExBenchmarks
import models.stringfuzzregextransformed
import models.stringfuzzregexgenerated
import models.automatark
import models.data
import models.SRE
import models.DRE
import startwebserver

import tools.cvc4
import tools.z3str3
import tools.regExSolverHeuristics
import tools.ostrich
import tools.z3seq
import tools.trau
import tools.IntersectionChecker


import summarygenerators
tracks = (models.SRE.getTrackData()+
          models.DRE.getTrackData()+
          []
          )

solvers = {}
for s in [
          tools.cvc4,
          tools.ostrich,
          tools.z3seq,
          tools.z3str3,
          tools.regExSolverHeuristics,
          tools.trau,
          tools.IntersectionChecker
          ]:
    s.addRunner (solvers)

summaries = [summarygenerators.terminalResult
             ]
timeout = 60
ploc = utils.JSONProgramConfig ()

store = storage.SQLiteDB ("ICTAC2023")
summaries = [
    summarygenerators.terminalResult,
    store.postTrackUpdate
]
# verifiers = ["cvc4","z3seq"]
verifiers = ["IntersectionChecker-CC","IntersectionChecker-EQ", "IntersectionChecker-PO", "IntersectionChecker-FA"]
testrunner().runTestSetup (tracks,solvers,voting.MajorityVoter(),summaries,store,timeout,ploc,verifiers)
startwebserver.Server (store.getDB ()).startServer ()
