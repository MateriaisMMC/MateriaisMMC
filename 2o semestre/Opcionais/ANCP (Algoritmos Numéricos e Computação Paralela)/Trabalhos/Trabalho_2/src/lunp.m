function [L, U] = lunp(A)
  % Get the dimensions of the matrix A
  n = size(A, 1);
  L = eye(n);
  U = A;

  % Perform LU decomposition
  for j = 1:n
    for i = j+1:n
      lij = U(i, j) / U(j, j);
      L(i, j) = lij;
      U(i, j:n) = U(i, j:n) - lij * U(j, j:n);
    end
  end
end