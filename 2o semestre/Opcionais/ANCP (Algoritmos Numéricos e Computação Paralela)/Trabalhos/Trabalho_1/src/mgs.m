function [Q, R] = mgs(A)
    [m, n] = size(A);
    Q = zeros(m, n);
    R = zeros(n, n);
    for i = 1 : n
      R(i, i) = norm(A(:, i));
      Q(:, i) = A(:, i) / R(i, i);
      for j = i + 1 : n
        R(i, j) = Q(:, i)' * A(:, j);
        A(:, j) = A(:, j) - R(i, j) * Q(:, i);
      end
    end
end