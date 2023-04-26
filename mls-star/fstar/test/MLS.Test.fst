module MLS.Test

open FStar.IO
open FStar.All
open MLS.Test.Types
open MLS.Test.Reader
open MLS.Test.FromExt.TreeMath
open MLS.Test.FromExt.CryptoBasics
open MLS.Test.FromExt.SecretTree
open MLS.Test.FromExt.MessageProtection
open MLS.Test.FromExt.KeySchedule
open MLS.Test.FromExt.PreSharedKeys
open MLS.Test.FromExt.TranscriptHashes
open MLS.Test.FromExt.Welcome
open MLS.Test.FromExt.TreeOperations
open MLS.Test.FromExt.TreeValidation
open MLS.Test.FromExt.Messages
open MLS.Test.FromExt.TreeKEM
open MLS.Test.Self.TreeKEM
open MLS.Test.Utils
open MLS.Test.Bench
open MLS.StringUtils

val run_tests: #a:Type -> string -> test_type -> ts_pre:(testsuite -> bool) -> (ts:testsuite{ts_pre ts} -> list a) -> (list a -> ML nat) -> ML unit
let run_tests #a name ty ts_pre extract_testsuite run_test =
  let testsuite = get_testsuite ty in
  if not (ts_pre testsuite) then
    failwith (name ^ ": failed to read tests")
  else (
    let testsuite = extract_testsuite testsuite in
    IO.print_string (name ^ ": running tests for 2/7 ciphersuites...\n");
    let n_run = run_test testsuite in
    IO.print_string (name ^ ": success!\n")
  )

let run_treemath_tests () =
  run_tests "Tree Math" TreeMath TreeMath_test? TreeMath_test?._0 test_treemath

let run_crypto_basics_tests () =
  run_tests "Crypto Basics" CryptoBasics CryptoBasics_test? CryptoBasics_test?._0 test_crypto_basics

let run_secret_tree_tests () =
  run_tests "Secret Tree" SecretTree SecretTree_test? SecretTree_test?._0 test_secret_tree

let run_message_protection_tests () =
  run_tests "Message Protection" MessageProtection MessageProtection_test? MessageProtection_test?._0 test_message_protection

let run_keyschedule_tests () =
  run_tests "Key Schedule" KeySchedule KeySchedule_test? KeySchedule_test?._0 test_keyschedule

let run_psk_tests () =
  run_tests "Pre-Shared Keys" PreSharedKeys PreSharedKeys_test? PreSharedKeys_test?._0 test_psk

let run_transcript_hashes_tests () =
  run_tests "Transcript Hashes" TranscriptHashes TranscriptHashes_test? TranscriptHashes_test?._0 test_transcript_hashes

let run_welcome_tests () =
  run_tests "Welcome" Welcome Welcome_test? Welcome_test?._0 test_welcome

let run_tree_operations_tests () =
  run_tests "Tree Operations" TreeOperations TreeOperations_test? TreeOperations_test?._0 test_tree_operations

let run_tree_validation_tests () =
  run_tests "Tree Validation" TreeValidation TreeValidation_test? TreeValidation_test?._0 test_tree_validation

let run_messages_tests () =
  run_tests "Messages" Messages Messages_test? Messages_test?._0 test_messages

let main =
  MLS.Test.Internal.test ();
  run_treemath_tests ();
  run_crypto_basics_tests ();
  run_secret_tree_tests ();
  run_message_protection_tests ();
  run_keyschedule_tests ();
  run_psk_tests ();
  run_transcript_hashes_tests ();
  run_welcome_tests ();
  run_tree_operations_tests ();
  run_tree_validation_tests ();
  run_messages_tests ();
  run_self_treekem_test ();
  bench {name = "adds"; n_message_rounds = 20; max_n_members = 10; do_removes = false;};
  bench {name = "messages"; n_message_rounds = 400; max_n_members = 3; do_removes = false;};
  bench {name = "removes"; n_message_rounds = 1; max_n_members = 15; do_removes = true;};
  ()
