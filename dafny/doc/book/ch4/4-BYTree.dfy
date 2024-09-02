datatype BYTree = BlueLeaf | YellowLeaf | Node(BYTree, BYTree)

function Example(): BYTree {
  Node(BlueLeaf, Node(YellowLeaf, BlueLeaf))
}

function BlueCount(t: BYTree): nat {
  match t
  case BlueLeaf => 1
  case YellowLeaf => 0
  case Node(left, right) => BlueCount(left) + BlueCount(right)
}

function LeftDepth(t: BYTree): nat {
  match t
  case BlueLeaf => 0
  case YellowLeaf => 0
  case Node(left, _) => 1 + LeftDepth(left)
}

predicate IsNode(t: BYTree) {
  match t
  case BlueLeaf => false
  case YellowLeaf => false
  case Node(_, _) => true
}

function GetLeft(t: BYTree): BYTree
  requires t.Node?
{
  match t
  case Node(left, _) => left
}
