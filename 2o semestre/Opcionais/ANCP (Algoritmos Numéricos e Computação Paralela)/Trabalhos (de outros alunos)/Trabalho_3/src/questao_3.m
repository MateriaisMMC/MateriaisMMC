function questao_3
    % Alinea a)
    A = [10 -3 6; -3 3 -2; 6 -2 1];
    y0 = [14,14933; -2,04765; 1,89832];
    [yk, lambda_k] = potencia(A, y0);
    disp('yk:');
    disp(yk);
    disp('lambda_k:');
    disp(lambda_k);
    
    % Alinea b)
    rayleight = (yk' * A * yk)/(yk' * yk);
    disp(rayleight)

    % Alinea c)
    A = (A - 1.89 * eye(3))^-1;
    y0 = [14,14933; -2,04765; 1,89832];
    [yk, lambda_k] = potencia(A, y0);
    disp('yk:');
    disp(yk);
    disp('lambda_k:');
    disp(lambda_k);

    % Alinea d)
    A = [10 -3 6; -3 3 -2; 6 -2 1];
    A = (A - 1.89 * eye(3));
    [L, U] = lunp(A);
    disp('L:')
    disp(L)
    disp('U:')
    disp(U);

    % Alinea e)
    A = [10 -3 6; -3 3 -2; 6 -2 1];
    p = 1.89;
    y0 = [0.32; 0.94; 0.03];
    [yk, lambda_k] = potinverso(A, p, y0);
    disp('Vetor yk: ');
    disp(yk)
    disp('Aproximação de lambda: ');
    disp(lambda_k);
end

function [yk, lambda_k] = potencia(A, y0)
    k = 0;
    yk = y0;
    lambda_k = y0(1);
    lambda_prev = inf;

    while abs(lambda_k - lambda_prev) >= 1e-1
        k = k + 1;
        y_tilde = A * yk;
        lambda_prev = lambda_k;
        lambda_k = max(abs(y_tilde));
        yk = y_tilde / lambda_k;
    end
end

function [yk, lambda_k] = potinverso(A, p, y0)
    % Calculo do valor e vetor próprio dominante de uma matriz A de ordem n,
    % dada uma translacao p
    % Parâmetros de entrada: matriz A, translacao p, epsilon
    % Parâmetros de saída: valor e vetor próprio dominante lambda_k e yk

    k = 0;
    n = size(A, 1);
    A_shifted = A - p * eye(n);
    [L, U] = lu(A_shifted); % função lu do MATLAB
    yk = y0;
    lambda_k = 0;

    while k < 2
        k = k + 1;
        y_tilde = U \ (L \ yk); % resolve_sistema(L, U, yk)
        lambda_k = max(abs(y_tilde)); % ykmax = max(|y_tilde|)
        yk = y_tilde / lambda_k;
    end

    lambda_k = 1 / lambda_k + p;
end