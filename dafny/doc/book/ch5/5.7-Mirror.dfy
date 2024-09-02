datatype Tree<T> = Leaf(data: T)
                 | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t: Tree<T>): Tree<T> {
  match t
  case Leaf(_) => t
  case Node(left, right) => Node(Mirror(right), Mirror(left))
}

lemma {:induction false} MirrorMirror<T>(t: Tree<T>)
  ensures Mirror(Mirror(t)) == t
{
  match t
  case Leaf(_) =>
    // trivial
  case Node(left, right) =>
    calc {
      Mirror(Mirror(Node(left, right)));
    ==  // def. Mirror (inner)
      Mirror(Node(Mirror(right), Mirror(left)));
    ==  // def. Mirror (outer)
      Node(Mirror(Mirror(left)), Mirror(Mirror(right)));
    ==  { MirrorMirror(left); MirrorMirror(right); } // I.H.
      Node(left, right);
    }
}

function Size<T>(t: Tree<T>): nat {
  match t
  case Leaf(_) => 1
  case Node(left, right) => Size(left) + Size(right)
}

lemma {:induction false} MirrorSize<T>(t: Tree<T>)
  ensures Size(Mirror(t)) == Size(t)
{
  match t
  case Leaf(_) =>
  case Node(left, right) =>
    calc {
      Size(Mirror(Node(left, right)));
    ==  // def. Mirror
      Size(Node(Mirror(right), Mirror(left)));
    ==  // def. Size
      Size(Mirror(right)) + Size(Mirror(left));
    ==  { MirrorSize(right); MirrorSize(left); } // I.H.
      Size(right) + Size(left);
    ==  // def. Size
      Size(Node(left, right));
    }
}
