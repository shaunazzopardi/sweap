class TypedValuation:
    def __init__(self, name: str, type: str, value):
        self.name = name
        self.type = type
        self.value = value

    def __str__(self) -> str:
        return str(self.name) + " : " + str(self.type) + " := " + str(self.value)
