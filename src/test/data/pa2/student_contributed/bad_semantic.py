x: UnknownClass = None
y: int = 1
y: bool = True
int: str = "bad"
z: int = 0

class B(NonExistentClass):
    pass

class Base(object):
    attr: int = 1

    def func(self: "Base", val: int) -> int:
        return val

class Derived(Base):
    attr: int = 2

    def bad_self(self: "Base") -> object:
        pass

    def func(self: "Derived", val: int) -> bool:
        return True

def test_scope() -> int:
    nonlocal missing_var
    z = 1
    pass

return 1