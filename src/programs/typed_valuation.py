class TypedValuation:
    def __init__(self, name: str, type: str, value):
        self.name = name
        self.type = type
        self.value = value

    def __str__(self) -> str:
        return str(self.name) + " : " + str(self.type) + " := " + str(self.value)

    def is_finite_state(self):
        if "bool" in self.type:
            return True
        if ".." in self.type:
            lo, hi = self.type.split("..")
            try:
                lo, hi = int(lo), int(hi)
                return True
            except ValueError:
                return False
