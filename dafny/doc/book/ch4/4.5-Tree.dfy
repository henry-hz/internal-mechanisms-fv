datatype Color = Blue | Yellow | Green | Red

datatype Tree<T> = Leaf(data: T)
                 | Node(left: Tree<T>, right: Tree<T>)

predicate AllBlue(t: Tree<Color>) {
  match t
  case Leaf(c) => c == Blue
  case Node(left, right) => AllBlue(left) && AllBlue(right) 
}

function Size<T>(t: Tree<T>): nat {
  match t
  case Leaf(_) => 1
  case Node(left, right) => Size(left) + Size(right)
}

lemma Test() {
  var a := Leaf(Color.Blue);
  var b := Leaf(Color.Yellow);
  var t := Tree.Node(a, b);

  assert Size(t) == Size(t) == 2;
}
