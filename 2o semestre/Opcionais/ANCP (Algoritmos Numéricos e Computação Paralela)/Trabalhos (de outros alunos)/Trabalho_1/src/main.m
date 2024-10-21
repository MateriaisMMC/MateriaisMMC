function main()
    % Pergunta 5 a)
    A = [1, 9, 0, 5, 3, 2; 
        -6, 3, 8, 2, -8, 0; 
        3, 15, 23, 2, 1, 7;
        3, 57, 35, 1, 7, 9;
        3, 5, 6, 15, 55, 2;
        33, 7, 5, 3, 5, 7];
    [Q, R] = mgs(A);
    Q
    % Pergunta 5 b)
    det_QR = det(Q * R)
    det_A = det(A)

    % Devido a uma maior establidade numérica dada pelo algoritmo de
    % Gram-Schimidt modificado obtemos, assim, o determinante da matriz QR
    % igual ao determinante da matriz A. 
    
    % Pergunta 6 b)
    B = randi(50, 200, 160);
    
    [Q, R] = mgsr(B, 1);
    [Q_s, R_s] = mgsr(B, 0);
    reorto = norm(Q' * Q - eye(160));
    sem_reorto = norm(Q_s' * Q_s - eye(160));
    
    reorto, sem_reorto
    erro_absoluto = abs(reorto - sem_reorto)

    % Podemos verificar através dos valores dados pelas variáveis `reorto`,
    % que representa o erro na ortogonalização com reortogonalização, e
    % `sem_reorto`, que representa o erro sem reortogonalização, que
    % obtemos valores de erro muito mais baixos aplicando o processo de
    % reortogonalização, sendo o erro absoluto representado pela variavel
    % `erro_absoluto`. Contudo, aplicar a reortogonalização conseguimos
    % obter valores mais precisos, no entanto, esta precisão tem um custo
    % no aumento da carga computacional.
