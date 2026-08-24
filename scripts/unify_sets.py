# This script is designed to be given a bunch of simp? outputs, and unifies them
#   but you could probably use it to unify any sets

print("Enter all sets, then hit enter once more")
print("Paste them without brackets, e.g.:")
print("  this, that, the other")

i = 1
print("Enter set 1: ", end="")
inp = input()
all_together = set()
while inp != "":
    inp = inp.replace("    ", " ")
    all_together |= set(inp.split(", "))
    i += 1
    print(f"Enter set {i}: ", end="")
    inp = input()

print(", ".join(all_together))