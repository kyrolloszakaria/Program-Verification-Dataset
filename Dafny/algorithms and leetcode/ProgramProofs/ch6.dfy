
module ListLibrary {
    datatype List<T> = Nil | Cons(head: T, tail: List<T>)
    
    function method Length<T>(xs: List<T>): nat {
        match xs
        case Nil => 0
        case Cons(_, tail) => 1 + Length(tail)
    }

    function method Snoc<T>(xs: List<T>, y: T): List<T> {
        match xs
        case Nil => Cons(y, Nil)
        case Cons(x, tail) => Cons(x, Snoc(tail, y))
    }

    lemma {:induction false} LengthSnoc<T>(xs: List<T>, x: T)
        ensures Length(Snoc(xs, x)) == Length(xs) + 1
    {
        var n := Length(xs);
        var res := Snoc(xs, x);
        match xs
        case Nil => 
        case Cons(y, ys) =>
            calc {
                Length(Snoc(xs, x));
                Length(Cons(y, Snoc(ys, x)));
                1 + Length(Snoc(ys, x));
                {LengthSnoc(ys, x);}
                1 + (n-1) + 1;
                Length(xs) + 1;
            }
    }

    function method Append<T>(xs: List<T>, ys: List<T>): List<T> 
        ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
    {
        match xs
        case Nil => ys
        case Cons(x, tail) => Cons(x, Append(tail, ys))
    }

    lemma {:induction false} LengthAppend<T>(xs: List<T>, ys: List<T>)
        // ensures Length(Append(xs, ys)) == Length(xs) + Length(ys); intrinsic properties on functions is not recommended
    {
        match ys
        case Nil =>
            match xs {
                case Nil =>
                    calc {
                        Length(Append<T>(xs,ys));
                        Length(Append<T>(Nil, Nil));
                        Length<T>(Nil);
                        0;
                        Length(xs) + Length(ys);
                    }
                case Cons(x, xxs) =>
                    calc {
                        Length(Append(xs, ys));
                        Length(Append(xs, Nil));
                        Length(Cons(x, Append(xxs, Nil)));
                        1 + Length(Append(xxs, Nil));
                        {LengthAppend(xxs, Nil);}
                        1 + Length(xxs);
                    }
            }
        case Cons(y, yys) =>
            match xs {
                case Nil =>
                    calc {
                        Length(Append<T>(xs, ys));
                        Length(Append(Nil, ys));
                        Length(ys);
                        Length(xs) + Length(ys);
                    }
                case Cons(x, xxs) =>
                    calc {
                        Length(Append(xs, ys));
                        Length(Cons(x, Append(xxs, ys)));
                        1 + Length(Append(xxs, ys));
                        {LengthAppend(xxs, ys);}
                        1 + Length(xs) - 1  + Length(ys);
                    }
            }
    }

    lemma {:induction false} SnocAppend<T>(xs: List<T>, y: T)
        ensures Snoc(xs, y) == Append(xs, Cons(y, Nil))
    {
        match xs {
            case Nil =>
            case Cons(x, tail) =>
                calc {

                } 
        }
    }
}

