function [Q, R] = mgsr(A, flag)
    [m, n] = size(A);
    Q = zeros(m, n);
    R = zeros(n, n);
    for j = 1 : n
      Q(:, j) = A(:, j);
      for i = 1 : j - 1
        R(i, j) = Q(:, i)' * Q(:, j);
        Q(:, j) = Q(:, j) - R(i, j) * Q(:, i);
      end
      if nargin == 1 || flag == 1
          for i = 1 : j - 1
              S(i, j) = Q(:, i)' * Q(:, j);
              Q(:, j) = Q(:, j) - S(i, j) * Q(:, i);
              R(i, j) = R(i, j) + S(i, j);
          end
      end
      R(j, j) = norm(Q(:, j));
      Q(:, j) = Q(:, j) / R(j, j);
    end
end