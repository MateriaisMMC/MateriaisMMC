function P=constroi_particao(d,N,K)
% d(i,j) - tem distancia de evento i ao representante j; N e numero de
% eventos; K numero de representantes

% para todos os eventos
% para todos os representantes
% ve qual a distancia minima do evento ao representante
% atribui à posicao i da particao o indice do representante mais proximo

 for i=1:N
  min=10000;
  for j=1:K
        if d(i,j)<min
            min=d(i,j);
            ind=j;
        end
  end
 P(i)=ind; 
 end
end