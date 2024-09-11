function [r,iteradas,est_erros] = metNewton(f,flinha,x0,tol,maxit,tab) 
    % metNewton  Implementa o método de Newton (para uma equação não linear)
    %
    % [r,iteradas,est_erros] = metNewton(f,flinha,x0,tol,maxit,tab) 
    %   Cálculo de uma sequência de aproximações para um zero de uma função 
    %   f (e de estimativas para os respetivos erros), usando o método de Newton .
    %   O processo iterativo é inicializado com uma aproximação inicial x0
    %   e é interrompido quando: 
    %      (i) o valor absoluto da diferença das duas últimas iteradas 
    %          calculadas (estimativa para o erro na penúltima iterada)
    %          for inferior a uma certa tolerância (tol)
    %                               ou 
    %    (ii) for atingido um número máximo de iterações permitidas 
    %     
    % INPUT:
    %   f: uma função, cujo zero pretendemos determinar
    %   flinha: uma função (derivada de f)
    %   x0: real (aproximação inicial)
    %
    % Opcionais:
    %   tol: real positivo (tolerância para estabelecer critério de paragem)
    %        Por defeito, tol = 0.5e-6
    %   maxit: inteiro positivo (número máximo de iterações a efetuar)
    %        Por defeito, maxit = 30
    %   tab: usar tab = 0, se não quisermos ver tabela de resultados no ecrã
    %        Por defeito, tab=1.
    %
    % OUTPUT:
    %  r:  aproximação para o zero de f
    %
    % Opcional:
    %   iteradas: (vetor coluna com as sucessivas) aproximações para o zero de f
    %   est_erros: (vetor coluna com as) estimativas para os erros nas aproximações
    %               

    %-------------------------------------------------------------------------
    % Verificar se existe o número mínimo de entradas
    %-------------------------------------------------------------------------
    if ( nargin < 3 )
       error('Tem de dar a função, a sua derivada e x0');
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
    iteradas = zeros(maxit,1); % Inicialização do vetor iteradas com zeros 
    est_erros = zeros(maxit,1);% Inicialização do vetor est_erros com zeros   
    iteradas(1) = x0; 
	for niter = 1:maxit+1 
        f0 = f(x0);
        flinha0 = flinha(x0);
        delta = f0/flinha0;
        x_nova= x0-delta;  % Cálculo da nova aproximação  
        est = abs(delta);   % Estimtiva para o erro em x0               
        est_erros(niter) = est;  % Atualização do vetor das estimativas
        if est < tol  
            break
        end
        iteradas(niter+1) = x_nova;
        x0 = x_nova; % Atualização de x0 com o valor da última iterada calculada 
	end

    if (niter == maxit+1 && est >= tol)
            disp(' ')
            disp(['Ao fim de ',num2str(maxit), ' iterações não se atingiu a precisão desejada'])
            disp(' ')         
    else
        disp(' ')
        disp(['Atingimos a precisão desejada em  ',num2str(niter-1), ' iterações']);
        disp(' ')
    end   
        iteradas(niter+1:end) = []; % "Eliminar" os valores não calculados                              
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