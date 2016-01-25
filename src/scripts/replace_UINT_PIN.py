## -*- coding: utf-8 -*-
##
## Copyright (C) - Triton
## This program is under the terms of the LGPLv3 License.
##

import sys
import os
import re

from distutils.dir_util import copy_tree
from time               import gmtime, strftime

path1 = r'\source\include\pin'
path2 = r'\extras\components\include'

def myreplace(path):

    #check if we already did the replacements
    if os.path.isdir(path + '_bak'):
        return

    copy_tree(path, path + '_bak')
    for root, dirs, files in os.walk(path):
        for name in files:
            try:
                file_full = root + '\\' + name

                f = open(file_full, 'r')
                all_file = f.read()

                #shutil.copy(file_full, file_full + '.bak')
                lines = all_file.split('\n')
                modified = str()
                for line in lines:
                    if 'IARG_UINT32' in line: # avoid replacing IARG_UINT32 type in types_vmapi.TLH
                        modified += line + '\n'
                    else:
                        modified += re.sub(r'(U?INT\d+?)', r'PIN_\1', line)
                        modified += '\n'
                f.close()
                f = open(file_full, 'w')
                f.write(modified)
                f.close()

            except Exception as e:
                print e
                exit()

myreplace(sys.argv[1] + path1)
myreplace(sys.argv[1] + path2)
print '*INT PIN types patch applied correctly :)'

