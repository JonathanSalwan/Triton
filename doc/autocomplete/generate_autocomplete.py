try:
    from typing import Optional, List, Dict, Tuple
except ImportError:
    pass

import re
import os

from collections import OrderedDict
from function import Function
from glob import glob

OBJECT_PREFIX = 'o'
NAMESPACE_PREFIX = 'n'

list_pattern      = r'\[(.*?)(?:,(?: ?...)?)?\]'
type_pattern      = r'(?P<type>List\[.*?\]|[\w\.]+)'
obj_doc_re        = re.compile(r'-\s<b>(?P<sig>.*?)<\/b><br>\r?\n(?P<desc>.*?)\r?\n\r?\n', flags=re.DOTALL)
name_doc_pattern  = r'- \*\*{namespace}\.(?P<member>.*?)\*\*'
ref_re            = re.compile(r'\\ref\spy_(.*?)_page')
sig_re            = re.compile(r'(?P<return>{}) (?P<name>\w+)\s?\((?P<args>.*?)\)'.format(type_pattern))
list_re           = re.compile(list_pattern)
obj_name_re       = re.compile(r'py(\w+)\.cpp')
namespace_name_re = re.compile(r'\\page py_(.*?)_page')


def sub_ref(match):
    return match.group(1)


def sub_types(s):
    # type: (str) -> str
    replacements = [
        ('integer', 'int'),
        ('string', 'str'),
        ('void', 'None'),
        ('function', 'Callable'),
        ('tuple', 'Tuple'),
    ]

    for to_repl, repl in replacements:
        s = re.sub(to_repl, repl, s)

    def sub_list(match):
        type_str = match.group(1)
        if ',' in type_str:
            type_str = 'Union[{}]'.format(type_str)
        return 'List[{}]'.format(type_str)

    s = list_re.sub(sub_list, s)
    return s


def gen_function(sig, desc):
    # type: (str, str) -> Optional[Function]
    dbg       = False and 'land' in sig
    sig       = sub_types(sig)
    sig_match = sig_re.search(sig)

    if not sig_match:
        print("error: could not match signature for\n '{}'".format(sig))
        print("pattern: {}".format(sig_re.pattern))
        return None

    # naming a function string... noice
    func_name = sig_match.group('name')
    if func_name == 'str':
        func_name = 'string'

    if dbg:
        for i, g in enumerate(sig_match.groups()):
            print('group {}: {}'.format(i, g))

    args_str = sig_match.group('args')
    args = OrderedDict() # type: dict
    for arg in args_str.split(','):
        arg_words = [a for a in arg.split(' ') if a]
        if not arg_words:
            print("error: could not find split arg into type/name for\n '{}', arg '{}'".format(args_str, arg))
            return None
        else:
            arg_type = arg_words[0]
            # in case there is no argument name specified
            if len(arg_words) < 2:
                # there is either a single argument None, i.e. no arg
                # where no argument name should be generated, i.e. empty str
                if arg_type == 'None':
                    arg_name = ''
                # or it is a variable arg, which means we generate a generic str
                else:
                    arg_name = 'args'
            else:
                arg_name = arg_words[1]

            if arg_name in args:
                print("error: argument name not unique\n '{}', arg_name '{}'".format(sig, arg_name))
                return None
            args[arg_name] = arg_type

    return Function(func_name, args, sig_match.group('return'), desc)


def gen_module_for_object(classname, input_str):
    # type: (str, str) -> str
    input_str = ref_re.sub(sub_ref, input_str)

    # find functions
    matches = obj_doc_re.finditer(input_str)
    funcs = []
    if not matches:
        return ""

    for match in matches:
        fsig = match.group('sig')
        desc = match.group('desc')
        # print("Signature: {}\nDescription: {}\n".format(fsig, desc))
        func = gen_function(fsig, desc)
        if func:
            funcs.append(func)
        else:
            print('... in module {}'.format(classname))

    # generate
    autogen_str = '''
class {classname}:
    def __init__(self, *args, **kargs):
        self.org = triton.{classname}(*args, **kargs)

    {functions}
'''.format(classname=classname, functions='\n'.join([str(f) for f in funcs]))

    return autogen_str


def gen_module_for_namespace(classname, input_str):
    # type: (str, str) -> str
    input_str = ref_re.sub(sub_ref, input_str)

    # find functions
    pat = name_doc_pattern.format(namespace=classname)
    matches = re.finditer(pat, input_str)
    members = []
    if not matches:
        return ""

    submodules = set()
    for match in matches:
        member = '    {member} = triton.{namespace}.{member}'.format(member = match.group('member'), namespace=classname)
        members.append(member)
        submod = member.split('=')[0].split('.')[:-1]
        for x in submod:
            submodules.add('    class %s: pass' % (x.lstrip()))

    #print(submodules)
    if not members:
        print("warning: empty namespace {}".format(classname))
        members.append('    pass')

    # generate
    autogen_str = '''
class {classname}:
{submodules}
{members}
'''.format(classname=classname, submodules='\n'.join(submodules), members='\n'.join(members))

    return autogen_str

def gen_reg_module_str(src_dir):
    # type: (str) -> str
    spec_path = os.path.join(src_dir, 'libtriton/includes/triton/x86.spec')
    with open(spec_path, 'r') as f:
        x86_reg_data = f.read()

    spec_path = os.path.join(src_dir, 'libtriton/includes/triton/aarch64.spec')
    with open(spec_path, 'r') as f:
        aarch64_reg_data = f.read()

    x86_regs = []
    reg_spec_pattern = r'REG_SPEC(_NO_CAPSTONE)?\((?P<name>.*?),.*?(?P<x86>false|true)\)'
    for match in re.finditer(reg_spec_pattern, x86_reg_data):
        x86_regs.append((match.group('name'), match.group('x86') == 'true'))

    aarch64_regs = []
    reg_spec_pattern = r'(SYS_)?REG_SPEC(_NO_CAPSTONE)?\((?P<name>.*?),.*?\)'
    for match in re.finditer(reg_spec_pattern, aarch64_reg_data):
        aarch64_regs.append(match.group('name'))

    if aarch64_regs[0] == 'UPPER_NAME':
        aarch64_regs = aarch64_regs[1:]

    class_str = '''
class {classname}:

{members}'''

    reg_module_str = '''
class REG:

    AARCH64 = AARCH64_class
    X86 = X86_class
    X86_64 = X86_64_class

'''

    enum_x86_regs = []
    enum_x86_64_regs = []
    enum_aarch64_regs = []

    for i, reg in enumerate(x86_regs):
        reg_name, is_x86 = reg
        member_str = '    {} = {}'.format(reg_name, i)
        if is_x86:
            enum_x86_regs.append(member_str)
        enum_x86_64_regs.append(member_str)

    for i, reg in enumerate(aarch64_regs):
        member_str = '    {} = {}'.format(reg, i)
        enum_aarch64_regs.append(member_str)

    mod_str = '{aarch64_class}\n\n{x86_class}\n\n{x86_64_class}\n\n{reg_class}'.format(
        reg_class=reg_module_str,
        x86_class=class_str.format(classname='X86_class', members='\n'.join(enum_x86_regs)),
        x86_64_class=class_str.format(classname='X86_64_class', members='\n'.join(enum_x86_64_regs)),
        aarch64_class=class_str.format(classname='AARCH64_class', members='\n'.join(enum_aarch64_regs)))

    return mod_str


def get_objects(object_dir):
    # type: (str) -> List[Tuple[str, str]]
    obj_paths = glob(object_dir + '/*.cpp')
    objs = [] # type: List[Tuple[str, str]]
    for obj_path in obj_paths:
        # find name of object from filename
        fname = os.path.basename(obj_path)
        name_match = obj_name_re.match(fname)
        if not name_match:
            print("error: could not match the object name regex\n {}\n {}".format(fname, obj_name_re.pattern))
            continue
        obj_name = name_match.group(1)
        objs.append((obj_path, obj_name))
    return objs


def get_namespaces(namespace_dir):
    # type: (str) -> List[Tuple[str, str]]
    name_paths = glob(namespace_dir + '/*.cpp')
    names = [] # type: List[Tuple[str, str]]
    for name_path in name_paths:

        if 'initSyscallNamespace' in name_path:
            print("info: skipping {}".format(name_path))
            continue
        # find name of namespace from doxygen page command
        with open(name_path, 'r') as f:
            data = f.read()

        name_match = namespace_name_re.search(data)
        if not name_match:
            print("error: could not match the namespace name regex\n {}\n {}".format(name_path, namespace_name_re.pattern))
            continue
        name_name = name_match.group(1)
        names.append((name_path, name_name))
    return names


def gen_init_file(modules):
    # type: (List[str]) -> str
    mod_str = """
from typing import List, Union, Callable, Tuple
import triton
try:
    import z3
except:
    pass

{modules}

raise ImportError
""".format(modules='\n\n'.join(modules))
    return mod_str


def main():
    this_dir = os.path.dirname(__file__)
    src_dir = os.path.join(this_dir, '../../src')
    namespace_dir = os.path.join(src_dir, 'libtriton/bindings/python/namespaces')
    object_dir = os.path.join(src_dir, 'libtriton/bindings/python/objects')

    out_dir = os.path.join(this_dir if len(os.sys.argv) < 2 else os.sys.argv[1], 'triton_autocomplete')
    if not os.path.exists(out_dir):
        os.mkdir(out_dir)

    # collect code for modules here
    modules = [] # type: List[str]

    # get names/paths for objects
    objs = get_objects(object_dir)

    # get names/paths for namespaces
    names = get_namespaces(namespace_dir)

    # generate modules for objects
    for obj_path, obj_name in objs:
        # read input file
        with open(obj_path, 'r') as f:
            input_str = f.read()

        # generate module str
        mod_str = gen_module_for_object(obj_name, input_str)
        modules.append(mod_str)

    # generate modules for namespaces
    for name_path, name_name in names:
        # read input file
        with open(name_path, 'r') as f:
            input_str = f.read()

        # generate module str
        if name_name == 'REG':
            mod_str = gen_reg_module_str(src_dir)
        else:
            mod_str = gen_module_for_namespace(name_name, input_str)
        modules.append(mod_str)

    # generate and create final __init__ file
    init_str = gen_init_file(modules)
    with open(os.path.join(out_dir, '__init__.py'), 'w') as f:
        f.write(init_str)

    print('autocomplete generation done')


if __name__ == '__main__':
    main()
