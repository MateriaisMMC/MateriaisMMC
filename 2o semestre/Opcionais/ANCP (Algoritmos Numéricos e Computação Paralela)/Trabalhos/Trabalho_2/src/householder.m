function v = householder(x)
    v = x;
    if v(1) > 0
        v(1) = v(1) + norm(x);
    else
        v(1) = v(1) - norm(x);
    end

    v = v / norm(v);

        