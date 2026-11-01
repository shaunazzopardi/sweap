from unittest import TestCase
from unittest.mock import patch

from main import process_args, setup_argument_parser


class TestTlsfInputFormat(TestCase):
    def test_cli_rejects_tlsf_with_other_formats_before_opening_files(self):
        parser = setup_argument_parser()
        for flag, extension in (('--issy', 'issy'), ('--rpg', 'rpg'), ('--tsl', 'tsl')):
            with self.subTest(flag=flag):
                args = parser.parse_args([
                    flag, 'missing.' + extension, '--tlsf', 'missing.tlsf', '--synthesise',
                ])
                with patch('builtins.open') as open_file:
                    with self.assertRaisesRegex(ValueError, r'only supported with \.prog'):
                        process_args(args)
                    open_file.assert_not_called()
