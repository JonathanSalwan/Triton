try:
    from typing import Dict, List, Set
except ImportError:
    pass

template = '''
    def {fname}({arg_names}):
        # type: ({arg_types}) -> {ret_type}
        """{doc_str}"""
        pass
'''

class Function():

    def __init__(self, name, args, ret_type, doc_str=''):
        # type: (str, Dict[str, str], str, str) -> None
        self.name          = name
        self.arg_types     = [{t} for t in args.values()]
        self.arg_names     = [{n} for n in args.keys()]
        self.ret_type      = ret_type
        self.doc_str       = doc_str
        self.overloaded_args = []

    def add_overload(self, other):
        assert(self.name == other.name)

        # we have fewer args than the other overload and need to expand them
        if len(self.arg_names) < len(other.arg_names):
            for i in range(len(self.arg_names), len(other.arg_names)):
                self.arg_names.append(set())
                self.arg_types.append(set())

        # create unions of the names and types
        for i in range(len(other.arg_names)):
            self.arg_names[i] |= other.arg_names[i]
            self.arg_types[i] |= other.arg_types[i]

    def __str__(self):
        # type: () -> str

        def handle_default_initializer(full_names):
            # type: (Set[str]) -> List[str]
            names = list(full_names)
            for i in range(len(names) - 1):
                # remove the default parameter for every arg except the last one
                if '=' in names[i]:
                    names[i] = names[i][:names[i].find('=')]

            return names

        arg_names = ', '.join(['self'] + ['_'.join(handle_default_initializer(names)) for names in self.arg_names])
        arg_types = 'Self'
        if len(self.arg_types) != 1 or len(self.arg_types[0]) > 1 or list(self.arg_types[0])[0] != 'None':
            arg_types = ', '.join(['Self'] + [' | '.join(types) for types in self.arg_types])
        func_str = template.format(
                     fname=self.name,
                     ret_type=self.ret_type,
                     arg_names=arg_names,
                     arg_types=arg_types,
                     doc_str=self.doc_str)
        return func_str
