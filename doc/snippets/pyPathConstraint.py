>>> from triton import TritonContext, ARCH
>>> ctxt = TritonContext()
>>> ctxt.setArchitecture(ARCH.X86_64)
>>> astCtxt = ctxt.getAstContext()

# TODO : Set up a real programm to test the behavior
# [Description]
>>> pcl = ctxt.getPathConstraints()
>>> for pc in pcl:
...     if pc.isMultipleBranches():
...         b1   =  pc.getBranchConstraints()[0]['constraint']
...         b2   =  pc.getBranchConstraints()[1]['constraint']
...
...         print 'Constraint branch 1:', b1
...         print 'Constraint branch 2:', b2
...
...         seed = list()
...
...         # Branch 1, we assume that the path constraint contains a symbolic variable
...         models  = ctxt.getModel(astCtxt.assert_(b1))
...         for k, v in models.items():
...             seed.append(v)
...
...         # Branch 2, we assume that the path constraint contains a symbolic variable.
...         models  = ctxt.getModel(astCtxt.assert_(b2))
...         for k, v in models.items():
...             seed.append(v)
...
...         if seed:
...             print 'B1: %s (%c)  |  B2: %s (%c)' % (seed[0], chr(seed[0].getValue()), seed[1], chr(seed[1].getValue()))
...

# [Description]
