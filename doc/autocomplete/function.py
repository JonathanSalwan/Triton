try:
    from typing import Dict, List
except ImportError:
    pass

from collections import OrderedDict

template = '''
    def {fname}({arg_names}):
        # type: ({arg_types}) -> {ret_type}
        """{doc_str}"""
{code}
'''

class Function():
    generate_code = True
    INDENT_STR = ' ' * 4
    DEBUG = False


    def __init__(self, name, args, ret_type, doc_str=''):
        # type: (str, Dict[str, str], str, str) -> None
        self.name       = name
        self.args       = OrderedDict(args)
        self.ret_type   = ret_type
        self.doc_str    = doc_str


    def gen_code(self):
        # type: () -> str
        code = str()
        func_call = '{}return self.org.{name}({args})'.format(self.INDENT_STR * 2, name=self.name, args=', '.join(self.args.keys()))
        if self.DEBUG:
            code += "{}print({})\n".format(self.INDENT_STR * 2, repr(func_call.strip()))
        code += func_call
        return code


    def __str__(self):
        # type: () -> str
        func_str = template.format(
                     fname=self.name,
                     ret_type=self.ret_type,
                     arg_names=', '.join(['self'] + list(self.args.keys())),
                     arg_types=', '.join('' if val == 'None' else val for val in self.args.values()),
                     doc_str=self.doc_str,
                     code='{}pass'.format(self.INDENT_STR * 2) if not self.generate_code else self.gen_code()
                   )
        return func_str
