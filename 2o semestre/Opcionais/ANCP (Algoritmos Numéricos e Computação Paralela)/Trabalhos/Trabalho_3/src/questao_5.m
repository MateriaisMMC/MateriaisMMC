function questao_5
    % Alinea a)
    A = hilb(4);
    T = householder_tridiagonal(A);
    
    % Display the results
    disp('Tridiagonal matrix T:');
    disp(T);
    
    % Alinea b)
    A = hilb(4);
    eigenvalues = qr_with_shift_deflation(A, 10);
    % Exibindo os autovalores
    disp('Valores Proprios:');
    disp(eigenvalues);


end

function eigenvalues = qr_with_shift_deflation(A, max_iter)
    % Redução para forma tridiagonal
    T = hess(A);
    n = size(T, 1);
    eigenvalues = zeros(n, 1);

    for k = n:-1:2
        iter = 0;
        while iter < max_iter
            iter = iter + 1;

            % Translação de origem
            mu = T(k, k);
            [Q, R] = qr(T(1:k, 1:k) - mu * eye(k));
            T(1:k, 1:k) = R * Q + mu * eye(k);

            % Verifica a convergência do valor próprio
            if abs(T(k, k-1)) < 10e-6
                eigenvalues(k) = T(k, k);
                T(k, k-1) = 0;
                T(k-1, k) = 0;
                break;
            end
        end
    end

    % Último autovalor
    eigenvalues(1) = T(1, 1);
end

function T = householder_tridiagonal(A)
    n = size(A, 1);
    T = A;
    Q = eye(n);
    
    for k = 1:n-2
        x = T(k+1:n, k);
        u = housevector(x);
        T(k+1:n, k:n) = T(k+1:n, k:n) - 2 * u * (u' * T(k+1:n, k:n));
        T(1:n, k+1:n) = T(1:n, k+1:n) - 2 * (T(1:n, k+1:n) * u) * u';
        
        Q(k+1:n, k+1:n) = Q(k+1:n, k+1:n) - 2 * u * u';
    end
end