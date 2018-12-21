from typing import Dict, List
from collections import OrderedDict

class Function():

    def __init__(self, name, args, ret_type, doc_str=''):
        # type: (str, Dict[str, str], str, str) -> None

        self.name = name
        self.args = OrderedDict(args)
        self.ret_type = ret_type
        self.doc_str = doc_str
    
    def __str__(self):
        # type: () -> str
        func_str = '''
    @staticmethod
    def {fname}({arg_names}):
        # type: ({arg_types}) -> {ret_type}
        """{doc_str}"""
        pass
            '''.format(fname=self.name, ret_type=self.ret_type,
            arg_names=', '.join(self.args.keys()),
            arg_types=', '.join('' if val == 'None' else val for val in self.args.values()),
            doc_str=self.doc_str)
        return func_str