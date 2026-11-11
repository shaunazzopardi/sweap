import unittest

from parsing.util.partitioned_update_chain import partition_updates
from prop_lang.biop import BiOp
from prop_lang.update import Update
from prop_lang.variable import Variable


class TestUpdatePartitioningSoundness(unittest.TestCase):
    def test_input_dependent_first_partition_index_zero_keeps_set_partition(self):
        i = Variable("i")
        x = Variable("x")
        y = Variable("y")

        updates = {
            "x": {Update(x, BiOp(y, "+", i))},
            "y": {Update(y, y)},
        }

        partitions, *_ = partition_updates(
            updates, [i], group_input_dependent_first=True
        )

        # If the first input-dependent component is already at index 0,
        # we still expect a set-based partition structure.
        self.assertIsInstance(partitions[0], set)
        self.assertEqual(partitions[0], {"x"})


if __name__ == "__main__":
    unittest.main()
