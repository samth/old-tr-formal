x = 100
z = 0
u = 0
v = 0
w = 1
d = 2
dd = x
while (dd > 0):
    w = w+w+w+w
    d = d+d
    dd = dd/2

while d > 0:
    if ((u + v + w) == x):
        z = z+d/2
        d = 0
    elif (u + v + w > x):
        d = d/2
        u = u
        v = v/2
        w = w/4
    else:
        z = z+d/2
        d = d/2
        u = u + v + w
        v = v/2 + w
        w = w/4

print z
