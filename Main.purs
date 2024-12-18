module Main where

import Prelude

import Data.Foldable (fold)
import Effect (Effect)
import TryPureScript (h1, h2, p, text, list, indent, link, render, code)

import Prelude
import Test.Unit (suite, test, assertEqual, assertTrue, assertFalse, Spec)
import Topology (containsEmptySet, containsParentSet, closedUnderUnions, closedUnderIntersections, isValidTopologySpace, isHausdorff, combinePairs)
import Data.Set (Set)
import Data.Set as Set
import Data.Array (fromFoldable)
import Data.Tuple (Tuple(..))
import Effect.Console (log)
import Test.Unit (runTest, Spec, suite)
import Data.Array (fromFoldable, length, index)
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Foldable (for_)

import Data.Set (Set)
import Data.Set as Set
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (fromFoldable)

-- Function to check if a set contains the empty set
containsEmptySet :: forall a. Set (Set a) -> Boolean
containsEmptySet topologySpace = Set.member Set.empty topologySpace

-- Function to check if a topology contains the parent set
containsParentSet :: forall a. Array a -> Set (Set a) -> Boolean
containsParentSet parentSet topologySpace = Set.member (Set.fromFoldable parentSet) topologySpace

-- Function to check if a topology is closed under arbitrary unions
closedUnderUnions :: forall a. Array a -> Set (Set a) -> Boolean
closedUnderUnions parentSet topologySpace = do
  let
    unions = map (\s1 -> map (\s2 -> Set.union s1 s2) (Set.toUnfoldable topologySpace) ) (Set.toUnfoldable topologySpace)
    flattenedUnions = concat unions
    allUnionsInTopology = all (\union -> Set.member union topologySpace) flattenedUnions
  allUnionsInTopology && containsParentSet parentSet topologySpace

-- Function to check if a topology is closed under finite intersections
closedUnderIntersections :: forall a. Array a -> Set (Set a) -> Boolean
closedUnderIntersections parentSet topologySpace = do
  let
    subsets = powerset topologySpace
    checkIntersection subset =
        case fromFoldable subset of
          Nothing -> Set.member (Set.fromFoldable parentSet) topologySpace
          Just (first : rest) ->
              let
                  intersection = foldl Set.intersection first rest
              in Set.member intersection topologySpace
    allIntersectionsInTopology = all checkIntersection subsets
  allIntersectionsInTopology

-- Function to check if a topology is valid
isValidTopologySpace :: forall a. Array a -> Set (Set a) -> Boolean
isValidTopologySpace parentSet topologySpace =
  containsEmptySet topologySpace &&
  containsParentSet parentSet topologySpace &&
  closedUnderUnions parentSet topologySpace &&
  closedUnderIntersections parentSet topologySpace

-- Function to check if a topology is Hausdorff
isHausdorff :: forall a. Ord a => Array a -> Set (Set a) -> Boolean
isHausdorff parentSet topology = do
  let
    toArrayList = fromFoldable

    containsAll :: Array a -> Array (Set a) -> Boolean
    containsAll arr topologyArr =
      all (\set -> any (\el -> Set.member el set) arr) topologyArr

    isValid :: Boolean = containsParentSet parentSet topology && containsEmptySet topology
    pairs :: Array (Tuple a a) = combinePairs parentSet

    checkHausdorff :: Tuple a a -> Boolean
    checkHausdorff (Tuple x y) = do
      let
        openSetsX = filter (any (\el -> el == x)) (toArrayList topology)
        openSetsY = filter (any (\el -> el == y)) (toArrayList topology)

        disjointExists u v = u /= v && Set.intersection u v == Set.empty

      any (\u -> any (\v -> disjointExists u v) openSetsY) openSetsX

  isValid && all checkHausdorff pairs

-- Helper function to generate all possible subsets of a set
powerset :: forall a. Set a -> Array (Set a)
powerset s =
  let
    sArr = fromFoldable s
    len = length sArr
    combine sub i = fromFoldable (map (\idx -> sArr !! idx) sub)
    subsets = map combine (foldr (\idx acc -> acc <> (map (\sub -> idx : sub) (acc))) [] (range 0 len ))
  in map Set.fromFoldable subsets

-- Helper function to generate all unique pairs in an Array
combinePairs :: forall a. Array a -> Array (Tuple a a)
combinePairs arr =
    concat $ map (\x -> map (\y -> Tuple x y) (filter (\y -> x /= y) arr)) arr


testContainsEmptySet :: Spec
testContainsEmptySet = suite "containsEmptySet" do
  test "Empty set present" do
    assertTrue $ containsEmptySet (Set.fromFoldable [Set.empty])
  test "Empty set not present" do
    assertFalse $ containsEmptySet (Set.fromFoldable [Set.fromFoldable [1]])
  test "Empty set present with others" do
    assertTrue $ containsEmptySet (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])

testContainsParentSet :: Spec
testContainsParentSet = suite "containsParentSet" do
  test "Parent set present" do
    assertTrue $ containsParentSet [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2]])
  test "Parent set not present" do
    assertFalse $ containsParentSet [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])
  test "Parent set singleton" do
    assertTrue $ containsParentSet [1] (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])

testClosedUnderUnions :: Spec
testClosedUnderUnions = suite "closedUnderUnions" do
  test "Simple valid union" do
    assertTrue $ closedUnderUnions [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2]])
  test "Valid unions with all subsets" do
    assertTrue $ closedUnderUnions [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [1, 2]])
  test "Invalid union (missing union result)" do
    assertFalse $ closedUnderUnions [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])

testClosedUnderIntersections :: Spec
testClosedUnderIntersections = suite "closedUnderIntersections" do
  test "Simple valid intersections" do
    assertTrue $ closedUnderIntersections [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2]])
  test "Valid intersections with all subsets" do
    assertTrue $ closedUnderIntersections [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [1, 2]])
  test "Invalid intersection (missing result)" do
     assertFalse $ closedUnderIntersections [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])
  test "Invalid intersections (missing empty set)" do
      assertFalse $ closedUnderIntersections [1, 2] (Set.fromFoldable [Set.fromFoldable [1]])

testIsValidTopologySpace :: Spec
testIsValidTopologySpace = suite "isValidTopologySpace" do
  test "Invalid (empty topology)" do
    assertFalse $ isValidTopologySpace [1, 2] (Set.fromFoldable [])
  test "Valid simple topology" do
    assertTrue $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2]])
  test "Valid with all subsets" do
    assertTrue $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [1, 2]])
  test "Invalid topology (missing parent set)" do
    assertFalse $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1]])
  test "Invalid topology (missing unions)" do
    assertFalse $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2]])
  test "Valid topology (valid union not valid intersection)" do
    assertTrue $ isValidTopologySpace [1,2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [1,2]])
  test "Invalid topology (invalid union)" do
    assertFalse $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.fromFoldable [1]])
  test "Invalid topology (duplicate empty set)" do
    assertFalse $ isValidTopologySpace [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2], Set.empty])


testIsHausdorff :: Spec
testIsHausdorff = suite "isHausdorff" do
    test "Hausdorff with separate sets" do
      assertTrue $ isHausdorff [1, 2] (Set.fromFoldable [Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [1, 2]])
    test "Hausdorff with all subsets" do
      assertTrue $ isHausdorff [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [1, 2]])
    test "Not hausdorff (only full set)" do
        assertFalse $ isHausdorff [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2]])
    test "Hausdorff with 3 variables" do
       assertTrue $ isHausdorff [1, 2, 3] (Set.fromFoldable [Set.fromFoldable [1], Set.fromFoldable [2], Set.fromFoldable [3], Set.fromFoldable [1, 2], Set.fromFoldable [2, 3], Set.fromFoldable [1, 2, 3], Set.empty])
    test "Hausdorff with 2 elements, only partial subsets" do
       assertTrue $ isHausdorff [1, 2] (Set.fromFoldable [Set.empty, Set.fromFoldable [1], Set.fromFoldable [1,2]])
    test "Not hausdorff (only full set - 3 elements)" do
       assertFalse $ isHausdorff [1, 2, 3] (Set.fromFoldable [Set.empty, Set.fromFoldable [1, 2, 3]])

testCombinePairs:: Spec
testCombinePairs = suite "testCombinePairs" do
    test "Combine 3 elements" do
      assertEqual (combinePairs [1,2,3]) (fromFoldable [Tuple 1 2,Tuple 1 3, Tuple 2 1, Tuple 2 3, Tuple 3 1, Tuple 3 2])
    test "Combine 2 elements" do
      assertEqual (combinePairs [1,2]) (fromFoldable [Tuple 1 2, Tuple 2 1])

mainTests :: Spec
mainTests = suite "All Tests" do
  testContainsEmptySet
  testContainsParentSet
  testClosedUnderUnions
  testClosedUnderIntersections
  testIsValidTopologySpace
  testIsHausdorff
  testCombinePairs

type TestResult = { name :: String, result :: String }
type TestTable = Array TestResult

-- Function to run tests, collect results
runTestsAndCollectResults :: Spec -> Effect TestTable
runTestsAndCollectResults testSuite = do
  results <- runTest testSuite
  let
     testCases = fromFoldable results
     table = map
        (\testCase ->
            let
                testName = String.joinWith "." $ fromFoldable $ testCase.name
                testResult = if testCase.isSuccess then "✅" else "❌"
            in { name: testName, result: testResult }
         ) testCases
  pure table

-- Function to render a test results table
renderTable :: TestTable -> Effect Unit
renderTable testTable = do
  let
    longestName = foldl (\acc res -> max acc (String.length res.name)) 0 testTable
    padString str len = str <> String.replicate (len - String.length str) " "
    header = "| " <> padString "Test Name" longestName <> " | Result |\n"
    divider = "|" <> String.replicate (longestName + 2) "-" <> "|--------|\n"
    row result = "| " <> padString result.name longestName <> " | " <> result.result <> " |\n"
    tableString = header <> divider <> foldMap row testTable
  log tableString

main :: Effect Unit
main = do
  testResults <- runTestsAndCollectResults testSuite
  renderTable testResults
