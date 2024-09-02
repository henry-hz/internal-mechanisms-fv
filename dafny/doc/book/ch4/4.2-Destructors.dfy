datatype BYTree = BlueLeaf
                | YellowLeaf
                | Node(left: BYTree, right: BYTree)

function BlueCount(t: BYTree): nat {
  if t.BlueLeaf? then 1
  else if t.YellowLeaf? then 0
  else BlueCount(t.left) + BlueCount(t.right)
}

method Test() {
  assert BlueCount(BlueLeaf) == 1;
  assert BlueCount(Node(YellowLeaf, BlueLeaf)) == 1;
}
