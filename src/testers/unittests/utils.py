"""Helper module for testing functions."""


def xfail(f):
    """Decorator to mark expected failing tests."""
    def wrapper(self, *args, **kwargs):
        """Expected fail function raise an exception."""
        with self.assertRaises(Exception):
            f(self, *args, **kwargs)
    return wrapper
