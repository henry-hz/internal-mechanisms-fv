datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(xs: List<T>): nat {
  if xs == Nil then 0 else 1 + Length'(xs.tail)
}

lemma LengthLength'<T>(xs: List<T>)
  ensures Length(xs) == Length'(xs)
{
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
  match xs
  case Nil => Cons(y, Nil)
  case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma LengthSnoc<T>(xs: List<T>, x: T)
  ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
}

function Append<T>(xs: List<T>, ys: List<T>): List<T>
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma LengthAppend<T>(xs: List<T>, ys: List<T>)
  ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
}

lemma SnocAppend<T>(xs: List<T>, y: T)
  ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
{
}

lemma {:induction false} AppendNil<T>(xs: List<T>)
  ensures Append(xs, Nil) == xs
{
  match xs
  case Nil =>
  case Cons(x, tail) =>
    calc {
      Append(xs, Nil);
    ==  // def. Append
      Cons(x, Append(tail, Nil));
    ==  { AppendNil(tail); }
      Cons(x, tail);
    ==
      xs;
    }
}

lemma AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
  ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
}

function Take<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then Nil else Cons(xs.head, Take(xs.tail, n - 1))
}

function Drop<T>(xs: List<T>, n: nat): List<T>
  requires n <= Length(xs)
{
  if n == 0 then xs else Drop(xs.tail, n - 1)
}

function LiberalTake<T>(xs: List<T>, n: nat): List<T>
{
  if n == 0 || xs == Nil then
    Nil
  else
    Cons(xs.head, LiberalTake(xs.tail, n - 1))
}

function LiberalDrop<T>(xs: List<T>, n: nat): List<T>
{
  if n == 0 || xs == Nil then
    xs
  else
    LiberalDrop(xs.tail, n - 1)
}

lemma TakesDrops<T>(xs: List<T>, n: nat)
  requires n <= Length(xs)
  ensures Take(xs, n) == LiberalTake(xs, n)
  ensures Drop(xs, n) == LiberalDrop(xs, n)
{
}

lemma AppendTakeDrop<T>(xs: List<T>, n: nat)
  requires n <= Length(xs)
  ensures Append(Take(xs, n), Drop(xs, n)) == xs
{
}

lemma TakeDropAppend<T>(xs: List<T>, ys: List<T>)
  ensures Take(Append(xs, ys), Length(xs)) == xs
  ensures Drop(Append(xs, ys), Length(xs)) == ys
{
}

function At<T>(xs: List<T>, i: nat): T
  requires i < Length(xs)
{
  if i == 0 then xs.head else At(xs.tail, i - 1)
}

lemma AtDropHead<T>(xs: List<T>, i: nat)
  requires i < Length(xs)
  ensures Drop(xs, i).Cons? && At(xs, i) == Drop(xs, i).head
{
}

lemma AtAppend<T>(xs: List<T>, ys: List<T>, i: nat)
  requires i < Length(Append(xs, ys))
  ensures At(Append(xs, ys), i)
       == if i < Length(xs) then
            At(xs, i)
          else
            At(ys, i - Length(xs))
{
}

function Find<T(==)>(xs: List<T>, y: T): nat
  ensures Find(xs, y) <= Length(xs)
{
  match xs
  case Nil => 0
  case Cons(x, tail) =>
    if x == y then 0 else 1 + Find(tail, y)
}

function SlowReverse<T>(xs: List<T>): List<T> {
  match xs
  case Nil => Nil
  case Cons(x, tail) => Snoc(SlowReverse(tail), x)
}

lemma LengthSlowReverse<T>(xs: List<T>)
  ensures Length(SlowReverse(xs)) == Length(xs)
{
  match xs
  case Nil =>
  case Cons(x, tail) =>
    LengthSnoc(SlowReverse(tail), x);
}

function ReverseAux<T>(xs: List<T>, acc: List<T>): List<T>
{
  match xs
  case Nil => acc
  case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}

lemma ReverseAuxSlowCorrect<T>(xs: List<T>, acc: List<T>)
  ensures ReverseAux(xs, acc) == Append(SlowReverse(xs), acc)
{
  match xs
  case Nil =>
  case Cons(x, tail) =>
    calc {
      Append(SlowReverse(xs), acc);
    ==  // def. SlowReverse
      Append(Snoc(SlowReverse(tail), x), acc);
    ==  { SnocAppend(SlowReverse(tail), x); }
      Append(Append(SlowReverse(tail), Cons(x, Nil)), acc);
    ==  { AppendAssociative(SlowReverse(tail), Cons(x, Nil), acc); }
      Append(SlowReverse(tail), Append(Cons(x, Nil), acc));
    ==  { assert Append(Cons(x, Nil), acc) == Cons(x, acc); }
      Append(SlowReverse(tail), Cons(x, acc));
    ==  { ReverseAuxSlowCorrect(tail, Cons(x, acc)); }
      ReverseAux(tail, Cons(x, acc));
    ==  // def. ReverseAux
      ReverseAux(xs, acc);
    }
}


function Reverse<T>(xs: List<T>): List<T> {
  ReverseAux(xs, Nil)
}

lemma ReverseCorrect<T>(xs: List<T>)
  ensures Reverse(xs) == SlowReverse(xs)
{
  calc {
    Reverse(xs);
  ==  // def. Reverse
    ReverseAux(xs, Nil);
  ==  { ReverseAuxSlowCorrect(xs, Nil); }
    Append(SlowReverse(xs), Nil);
  ==  { AppendNil(SlowReverse(xs)); }
    SlowReverse(xs);
  }
}

lemma ReverseAuxCorrect<T>(xs: List<T>, acc: List<T>)
  ensures ReverseAux(xs, acc) == Append(Reverse(xs), acc)
{
  ReverseCorrect(xs);
  ReverseAuxSlowCorrect(xs, acc);
}

lemma LengthReverse<T>(xs: List<T>)
  ensures Length(Reverse(xs)) == Length(xs)
{
  ReverseCorrect(xs);
  LengthSlowReverse(xs);
}

lemma ReverseAuxAppend<T>(xs: List<T>, ys: List<T>, acc: List<T>)
  ensures ReverseAux(Append(xs, ys), acc)
       == Append(Reverse(ys), ReverseAux(xs, acc))
{
  match xs
  case Nil =>
    ReverseAuxCorrect(ys, acc);
  case Cons(x, tail) =>
}

lemma AtReverse<T>(xs: List<T>, i: nat)
  requires i < Length(xs)
  ensures (LengthReverse(xs);
    At(xs, i) == At(Reverse(xs), Length(xs) - 1 - i))
{
  var x, tail := xs.head, xs.tail;
  LengthReverse(xs);
  calc {
    At(Reverse(xs), Length(xs) - 1 - i);
  ==  // def. Reverse
    At(ReverseAux(xs, Nil), Length(xs) - 1 - i);
  ==  // def. ReverseAux
    At(ReverseAux(tail, Cons(x, Nil)), Length(xs) - 1 - i);
  ==  { ReverseAuxSlowCorrect(tail, Cons(x, Nil)); }
    At(Append(SlowReverse(tail), Cons(x, Nil)), Length(xs) - 1 - i);
  ==  { ReverseCorrect(tail); }
    At(Append(Reverse(tail), Cons(x, Nil)), Length(xs) - 1 - i);
  ==  { AtAppend(Reverse(tail), Cons(x, Nil), Length(xs) - 1 - i); }
    if Length(xs) - 1 - i < Length(Reverse(tail)) then
      At(Reverse(tail), Length(xs) - 1 - i)
    else
      At(Cons(x, Nil), Length(xs) - 1 - i-Length(Reverse(tail)));
  ==  { LengthReverse(tail); }
    if Length(xs) - 1 - i < Length(tail) then
      At(Reverse(tail), Length(xs) - 1 - i)
    else
      At(Cons(x, Nil), Length(xs) - 1 - i - Length(tail));
  ==  // arithmetic, using Length(xs) == Length(tail) + 1 and 0 <= i
    if 0 < i then
      At(Reverse(tail), Length(tail) - 1 - (i - 1))
    else
      At(Cons(x, Nil), 0);
  }
  if 0 < i {
    LengthReverse(tail);
    calc {
      At(Reverse(tail), Length(tail) - 1 - (i - 1));
    ==  { AtReverse(tail, i - 1); }
      At(tail, i - 1);
    ==  // def. At
      At(xs, i);
    }
  }
}
