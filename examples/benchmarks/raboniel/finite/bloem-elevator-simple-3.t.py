import json
import readline

def run(init, inputs):
  state = 0
  c_floor = init['c_floor']
  for _input in inputs:
    if state == 0 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor - 1)

    if state == 0 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and 3 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and not (c_floor == 3) and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and c_floor == 3 and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and not (c_floor == 3) and not (c_floor == 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and c_floor == 3 and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and 3 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and not (c_floor == 3) and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and c_floor == 3 and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and not (c_floor == 3) and not (c_floor == 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and not (3 >= c_floor))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and c_floor == 3 and c_floor == 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 2) and not (c_floor == 3) and c_floor == 1 and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and not (c_floor == 3) and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((not (c_floor == 2) and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and not (c_floor >= 1))):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 2 and c_floor == 3 and not (c_floor == 1) and 3 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    state = state_prime
    c_floor = c_floor_prime
    yield {'c_floor':c_floor}


def main():
  def readInputs():
    while True:
      raw = input("inputs: ")
      if raw == "exit":
        break
      yield json.loads(raw)

  inputs = readInputs()
  raw = input("initial state: ")
  init = json.loads(raw)
  outputs = run(init, inputs)
  for o in outputs:
    print("state: ", o)
    print("-----")

if __name__ == "__main__":
    main()

