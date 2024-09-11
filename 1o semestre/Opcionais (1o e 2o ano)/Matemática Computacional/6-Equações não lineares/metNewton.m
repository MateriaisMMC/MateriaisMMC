function [r,iteradas,est_erros] = metNewton(f,flinha,x0,tol,maxit,tab) 
    % metNewton  Implementa o m�todo de Newton (para uma equa��o n�o linear)
    %
    % [r,iteradas,est_erros] = metNewton(f,flinha,x0,tol,maxit,tab) 
    %   C�lculo de uma sequ�ncia de aproxima��es para um zero de uma fun��o 
    %   f (e de estimativas para os respetivos erros), usando o m�todo de Newton .
    %   O processo iterativo � inicializado com uma aproxima��o inicial x0
    %   e � interrompido quando: 
    %      (i) o valor absoluto da diferen�a das duas �ltimas iteradas 
    %          calculadas (estimativa para o erro na pen�ltima iterada)
    %          for inferior a uma certa toler�ncia (tol)
    %                               ou 
    %    (ii) for atingido um n�mero m�ximo de itera��es permitidas 
    %     
    % INPUT:
    %   f: uma fun��o, cujo zero pretendemos determinar
    %   flinha: uma fun��o (derivada de f)
    %   x0: real (aproxima��o inicial)
    %
    % Opcionais:
    %   tol: real positivo (toler�ncia para estabelecer crit�rio de paragem)
    %        Por defeito, tol = 0.5e-6
    %   maxit: inteiro positivo (n�mero m�ximo de itera��es a efetuar)
    %        Por defeito, maxit = 30
    %   tab: usar tab = 0, se n�o quisermos ver tabela de resultados no ecr�
    %        Por defeito, tab=1.
    %
    % OUTPUT:
    %  r:  aproxima��o para o zero de f
    %
    % Opcional:
    %   iteradas: (vetor coluna com as sucessivas) aproxima��es para o zero de f
    %   est_erros: (vetor coluna com as) estimativas para os erros nas aproxima��es
    %               

    %-------------------------------------------------------------------------
    % Verificar se existe o n�mero m�nimo de entradas
    %-------------------------------------------------------------------------
    if ( nargin < 3 )
       error('Tem de dar a fun��o, a sua derivada e x0');
    end
    %-------------------------------------------------------------------
    %       Valores de argumentos por defeito
    %--------------------------------------------------------------------------   
    if ( nargin <6  ); tab = 1; end
    if ( nargin <5 || isempty(maxit) ); maxit = 30; end
    if ( nargin <4 || isempty(tol)); tol = 0.5e-6; end
    %------------------------------------------------------------------------
    %              PROCESSO ITERATIVO
    %------------------------------------------------------------------------
    iteradas = zeros(maxit,1); % Inicializa��o do vetor iteradas com zeros 
    est_erros = zeros(maxit,1);% Inicializa��o do vetor est_erros com zeros   
    iteradas(1) = x0; 
	for niter = 1:maxit+1 
        f0 = f(x0);
        flinha0 = flinha(x0);
        delta = f0/flinha0;
        x_nova= x0-delta;  % C�lculo da nova aproxima��o  
        est = abs(delta);   % Estimtiva para o erro em x0               
        est_erros(niter) = est;  % Atualiza��o do vetor das estimativas
        if est < tol  
            break
        end
        iteradas(niter+1) = x_nova;
        x0 = x_nova; % Atualiza��o de x0 com o valor da �ltima iterada calculada 
	end

    if (niter == maxit+1 && est >= tol)
            disp(' ')
            disp(['Ao fim de ',num2str(maxit), ' itera��es n�o se atingiu a precis�o desejada'])
            disp(' ')         
    else
        disp(' ')
        disp(['Atingimos a precis�o desejada em  ',num2str(niter-1), ' itera��es']);
        disp(' ')
    end   
        iteradas(niter+1:end) = []; % "Eliminar" os valores n�o calculados                              
        est_erros(niter+1:end)= [];
        r = iteradas(end);   
    if tab ~=0
        n_iteradas=length(iteradas);
        tabela=[(0: n_iteradas-1)',iteradas,est_erros]';
        disp('_______________________________')
        disp(['  k ','      x_k   ', '    Est. erro  '])
        disp('_______________________________')
        fprintf('%3.0f   %10.6f   %10.2e\n',tabela)
        disp('_______________________________')
    end
end