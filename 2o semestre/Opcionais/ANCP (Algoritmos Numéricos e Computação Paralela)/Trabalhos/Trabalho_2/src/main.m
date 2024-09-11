function main()
    % Pergunta 3
    % b)
    rand_x = randi(100, 10,1);
    disp('rand_x');
    disp(rand_x);
    [x, beta] = housevector(rand_x);
    disp('x:')
    disp(x)
    disp('beta:')
    disp(beta)
    % c)
    qr_solve()

    % Pergunta 4
    lu_solve()
    ul_solve()
end

function qr_solve()
    A = hilb(10);
    b = ones(10, 1);
    [Q, R] = qrhouseholder(A);
    relative_residue(Q, R, A, b)
end

function relative_residue(Q, R, A, b)
    Q_tb = Q' * b;
    x_qr = inv(R) * Q_tb;
    x_matlab = A \ b;
    disp('x_qr:');
    disp(x_qr);
    disp('x_matlab');
    disp(x_matlab);

    r_qr = b - A * x_qr;
    r_matlab = b - A * x_matlab;
    
    norm_A = norm(A);
    norm_r_qr = norm(r_qr);
    norm_r_matlab = norm(r_matlab);
    
    relative_residue_qr = norm_r_qr / norm_A * norm(b);
    relative_residue_matlab = norm_r_matlab / norm_A * norm(b);

    disp('relative_residue_qr');
    disp(relative_residue_qr);
    disp('relative_residue_matlab');
    disp(relative_residue_matlab);
end

function lu_solve()
    A = [[1, 1, 1, 4]; 
        [1, 2, 4, 5]; 
        [1, 3, 9, 2]; 
        [1, 5, 1, 2]];
    [L, U] = lunp(A);
    L, U
end

function ul_solve()
    A = [[1, 1, 1, 4]; 
        [1, 2, 4, 5]; 
        [1, 3, 9, 2]; 
        [1, 5, 1, 2]];
    [L, U] = ulnp(A);
    L, U
end
    