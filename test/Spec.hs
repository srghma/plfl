import Test.Hspec
import Topology
import Data.Set (fromList, empty)

main :: IO ()
main = hspec $ do
    describe "Topology Functions" $ do

        describe "containsEmptySet" $ do
            it "should return True if the set contains the empty set" $
                containsEmptySet (fromList [fromList []]) `shouldBe` True
            it "should return False if the set does not contain the empty set" $
                containsEmptySet (fromList [fromList [1]]) `shouldBe` False
            it "should return True if the set contains the empty set among others" $
                containsEmptySet (fromList [fromList [], fromList [1]]) `shouldBe` True

        describe "containsParentSet" $ do
            it "should return True if the topology contains the parent set" $
                containsParentSet (fromList [1, 2]) (fromList [fromList [], fromList [1, 2]]) `shouldBe` True
            it "should return False if the topology does not contain the parent set" $
                containsParentSet (fromList [1, 2]) (fromList [fromList [], fromList [1]]) `shouldBe` False
            it "should return True if the topology contains the parent set" $
                containsParentSet (fromList [1]) (fromList [fromList [], fromList [1]]) `shouldBe` True

        describe "closedUnderUnions" $ do
            it "should return True if the topology is closed under unions" $
                closedUnderUnions (fromList [1, 2]) (fromList [fromList [], fromList [1, 2]]) `shouldBe` True
            it "should return True if the topology is closed under unions" $
                closedUnderUnions (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2], fromList [1, 2]]) `shouldBe` True
            it "should return False if the topology is not closed under unions" $
                closedUnderUnions (fromList [1, 2]) (fromList [fromList [], fromList [1]]) `shouldBe` False

        describe "closedUnderIntersections" $ do
            it "should return True if the topology is closed under intersections" $
                closedUnderIntersections (fromList [1, 2]) (fromList [fromList [], fromList [1, 2]]) `shouldBe` True
            it "should return True if the topology is closed under intersections" $
                closedUnderIntersections (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2], fromList [1, 2]]) `shouldBe` True
            it "should return False if the topology is not closed under intersections" $
                closedUnderIntersections (fromList [1, 2]) (fromList [fromList [], fromList [1]]) `shouldBe` False
            it "should return False if the topology is not closed under intersections" $
                closedUnderIntersections (fromList [1, 2]) (fromList [fromList [1]]) `shouldBe` False

        describe "isAValidTopologySpace" $ do
            it "should return False if the topology is not valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList []]) `shouldBe` False
            it "should return True if the topology is valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1, 2]]) `shouldBe` True
            it "should return True if the topology is valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2], fromList [1, 2]]) `shouldBe` True
            it "should return False if the topology is not valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1]]) `shouldBe` False
            it "should return False if the topology is not valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2]]) `shouldBe` False
            it "should return True if the topology is valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [1, 2]]) `shouldBe` True
            it "should return False if the topology is not valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [1]]) `shouldBe` False
            it "should return False if the topology is not valid" $
                isAValidTopologySpace (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2], fromList []]) `shouldBe` False

        describe "isHausdorff" $ do
             it "should return True if the topology is Hausdorff" $
                 isHausdorff (fromList [1, 2]) (fromList [fromList [1], fromList [2], fromList [1, 2]]) `shouldBe` True
             it "should return True if the topology is Hausdorff" $
                 isHausdorff (fromList [1, 2]) (fromList [fromList [], fromList [1], fromList [2], fromList [1, 2]]) `shouldBe` True
             it "should return False if the topology is not Hausdorff" $
                 isHausdorff (fromList [1, 2]) (fromList [fromList [], fromList [1, 2]]) `shouldBe` False
             it "should return True if the topology is Hausdorff" $
                 let a = "a"; b = "b"; c = "c" in
                   isHausdorff (fromList [a, b, c]) (fromList [fromList [a], fromList [b], fromList [c], fromList [a, b], fromList [b, c], fromList [a, b, c], fromList []]) `shouldBe` True
             it "should return True if the topology is Hausdorff" $
                 isHausdorff (fromList [1,2]) (fromList [fromList [], fromList [1], fromList [1,2]]) `shouldBe` True
             it "should return False if the topology is not Hausdorff" $
                 isHausdorff (fromList [1,2,3]) (fromList [fromList [], fromList [1,2,3]]) `shouldBe` False
