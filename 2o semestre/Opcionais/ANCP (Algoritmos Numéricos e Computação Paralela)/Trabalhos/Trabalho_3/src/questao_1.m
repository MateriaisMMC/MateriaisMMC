function questao_1
    A = [1 0 1; 1 1 1; 0 0 1; 1 1 1; 0 1 1; 1 1 0];
    [m, n] = size(A);
    A_norm_2 = norm(A, 2);
    A_inf = norm(A, inf);
    A_1 = norm(A, 1);
    if A_inf / sqrt(n) <= A_norm_2 && A_norm_2 <= sqrt(m) * A_inf
        fprintf("%d <= %d <= %d\nTrue\n", A_inf / sqrt(n), A_norm_2, sqrt(m) * A_inf);
    end

    if A_1 / sqrt(m) <= A_norm_2 && A_norm_2 <= sqrt(n) * A_1
        fprintf("%d <= %d <= %d\nTrue\n", A_1 / sqrt(m), A_norm_2, sqrt(n) * A_1);
    end
end