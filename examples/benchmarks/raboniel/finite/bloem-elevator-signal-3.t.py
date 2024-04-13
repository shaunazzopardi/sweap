import json
import readline

def run(init, inputs):
  state = 0
  floor = init['floor']
  target = init['target']
  for _input in inputs:
    signal = _input['signal']
    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and floor == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target and target == 2 and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and target == 3 and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = signal

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target and not (target == 2) and target == 3 and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3 and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor + 1)
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and floor == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target and not (target == 2))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = signal

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and target == 3 and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3 and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target and target == 2 and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and target == 2 and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target and target == 2 and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and not (signal >= 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and not (floor == 1))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and not (3 >= floor))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target and not (target == 2) and target == 3 and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = floor
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target and not (target == 2) and not (target == 3) and target == 1 and not (target == 0))):
      state_prime = 0
      floor_prime = floor
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target and target == 2 and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = floor
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3 and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and target == 2 and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and target == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and not (floor == 1))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and floor == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = floor
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and not (floor >= 1))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target and not (target == 2) and not (target == 3) and target == 1 and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and target == 3 and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor + 1)
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and target == 2 and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and target == 1 and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and floor == target)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target and not (target == 2) and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target and not (target == 2) and not (target == 3))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and target == 2 and not (target == 3) and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor + 1)
      target_prime = target

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and not (floor == 3) and floor == 1 and floor == target and not (target == 2) and not (target == 3) and not (target == 1))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and floor == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and floor == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target and not (target == 2) and target == 3 and not (target == 1) and not (target == 0))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and not (target == 3) and target == 1 and target == 0)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and not (floor == 1) and floor == target and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and not (floor == 2) and not (floor == 3) and floor == 1 and not (floor == target) and not (target == 2) and not (target == 3) and not (target == 1) and target == 0)):
      state_prime = 0
      floor_prime = floor
      target_prime = signal

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and not (floor == 2) and floor == 3 and floor == 1)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and not (signal == 0) and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and not (target == 2) and target == 3)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((not (3 >= signal))):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    if state == 0 and ((3 >= signal and 3 >= floor and signal >= 0 and floor >= 1 and signal == 0 and floor == 2 and not (floor == 3) and not (floor == 1) and not (floor == target) and target == 2)):
      state_prime = 0
      floor_prime = (floor - 1)
      target_prime = 0

    state = state_prime
    floor = floor_prime
    target = target_prime
    yield {'floor':floor, 'target':target}


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

