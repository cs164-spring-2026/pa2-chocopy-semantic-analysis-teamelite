class A(object):
    val: int = 0

def expect_int(x: int) -> int:
    return x

a: A = None
my_list: [int] = None
x: int = 0

a = A()
my_list = [1, 2, 3]

my_list["bad"] + 10
(1 + "a") * 5
expect_int(True) + 1
a.val = "string"

for x in True:
    pass

if 1 == "1":
    pass