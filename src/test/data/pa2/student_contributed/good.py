global_count: int = 0
my_list: [int] = None

class Animal(object):
    age: int = 0
    name: str = "Unknown"

    def __init__(self: "Animal"):
        self.age = 1
        self.name = "Animal"

    def speak(self: "Animal") -> str:
        return "..."

class Dog(Animal):
    is_good_boy: bool = True

    def __init__(self: "Dog"):
        self.age = 3
        self.name = "Doggo"

    def speak(self: "Dog") -> str:
        return "Woof!"

def process_data(x: int, y: int) -> int:
    global global_count
    z: int = 0

    def helper() -> object:
        nonlocal z
        global global_count
        z = (x + y) * 2 // 3 % 4
        global_count = global_count + 1

    helper()

    if z == 0 or x != y:
        return z
    elif x <= y and x >= y:
        return -z
    else:
        return 0

my_list = [1, 2, 3] + [4, 5]
for global_count in my_list:
    if global_count > 3:
        process_data(global_count, 1)

while global_count < 10:
    global_count = global_count + 1

print(Dog().speak())