from z3 import *

X = Real('X')
Y = Real('Y')

s = Solver()

s.add(X**2 + Y**2 == 1)
if (s.check() == sat):
    m = s.model()
print(m)

x, y = Bools('x y')

solve = Solver()

constraint1 = x
constraint2 = y
constraint3 = Or(x, y)

solve.add(constraint1, constraint2, constraint3)
if (solve.check() == sat):
    model = solve.model()
    print(model)