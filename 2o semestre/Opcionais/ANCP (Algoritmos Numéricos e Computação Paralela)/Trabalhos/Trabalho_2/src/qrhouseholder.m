function [Q, R]= qrhouseholder(A)
    [m, n] = size(A);
    Q = eye(m);

    for j = 1 : n
        x = A(j:m, j);
        [v, ~] = housevector(x);
        A(j:m, :) = A(j:m, :) - 2 * v * (v' * A(j:m, :));
        Q(:, j:m) = Q(:, j:m) - 2 * (Q(:, j:m) * v) * v';
    end
    R = A;
        