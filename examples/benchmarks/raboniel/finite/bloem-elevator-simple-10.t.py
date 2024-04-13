import json
import readline

def run(init, inputs):
  state = 0
  c_floor = init['c_floor']
  for _input in inputs:
    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = c_floor

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor - 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 0 and ((c_floor == 9 and c_floor == 8 and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor - 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor - 1)

    if state == 0 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 0 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = c_floor

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 1 and ((c_floor == 9 and c_floor == 8 and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor - 1)

    if state == 1 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor - 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor - 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor - 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 2 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10 and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4 and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 3
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3 and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = c_floor

    if state == 3 and ((c_floor == 9 and c_floor == 8 and c_floor == 7)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 1
      c_floor_prime = (c_floor - 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and c_floor == 10)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and c_floor == 1 and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor - 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and c_floor == 5)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((c_floor == 9 and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and c_floor == 8 and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and c_floor == 3)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and c_floor == 5 and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and not (c_floor >= 1))):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and c_floor == 7 and not (c_floor == 6) and not (c_floor == 5) and c_floor == 4)):
      state_prime = 0
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and not (c_floor == 6) and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and c_floor == 2 and not (c_floor == 10) and not (c_floor == 1) and 10 >= c_floor and c_floor >= 1)):
      state_prime = 2
      c_floor_prime = (c_floor + 1)

    if state == 3 and ((not (c_floor == 9) and not (c_floor == 8) and not (c_floor == 7) and c_floor == 6 and not (c_floor == 5) and not (c_floor == 4) and not (c_floor == 3) and not (c_floor == 2) and not (c_floor == 10) and not (c_floor == 1) and not (10 >= c_floor))):
      state_prime = 0
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

