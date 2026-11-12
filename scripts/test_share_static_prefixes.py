#!/usr/bin/env python3
"""Regression tests for sharing generated static-mode prefixes."""
import importlib.util
import unittest
from pathlib import Path

path = Path(__file__).with_name('share_static_prefixes.py')
spec = importlib.util.spec_from_file_location('share_static_prefixes', path)
share_static_prefixes = importlib.util.module_from_spec(spec)
spec.loader.exec_module(share_static_prefixes)


def fixture(extra='', stack='hstack'):
    pre = '\n'.join(['  let r0 := h'] + [
        f'  have r{i} := RD.step r{i - 1} (by native_decide) {extra}'
        for i in range(1, 7)
    ])
    return f'''/-- Automatically generated RD summary. -/
theorem block_taken {{x : Nat}}
    (hstack : StackOK x)
    (h : RD x)
    : Result := by
{pre}
  exact finish r6

/-- Static-mode twin. -/
theorem block_static {{x : Nat}}
    ({stack} : StackOK x)
    (hperm : perm = false)
    (h : RD x)
    : RDstatic := by
{pre}
  exact RD.sstoreStatic r6 hperm

end Namespace
'''


class ShareStaticPrefixesTests(unittest.TestCase):
    def test_matching_prefix_is_shared_and_idempotent(self):
        source = fixture()
        shared, count = share_static_prefixes.share(source)
        self.assertEqual(count, 1)
        self.assertEqual(shared.count('private def block_before_static'), 1)
        self.assertEqual(shared.count('block_before_static hstack h'), 2)
        self.assertEqual(shared.count('native_decide'), 6)
        for header in ('theorem block_taken {x : Nat}', 'theorem block_static {x : Nat}'):
            self.assertIn(header, shared)
        self.assertEqual(share_static_prefixes.share(shared), (shared, 0))

    def test_guarded_prefix_is_not_shared(self):
        source = fixture(extra='hguard0')
        self.assertEqual(share_static_prefixes.share(source), (source, 0))

    def test_different_stack_hypothesis_is_not_shared(self):
        source = fixture(stack='other')
        self.assertEqual(share_static_prefixes.share(source), (source, 0))

    def test_different_instruction_prefix_is_not_shared(self):
        source = fixture().replace('RD.step r5 (by native_decide)', 'RD.other r5 (by native_decide)', 1)
        self.assertEqual(share_static_prefixes.share(source), (source, 0))


if __name__ == '__main__':
    unittest.main()
