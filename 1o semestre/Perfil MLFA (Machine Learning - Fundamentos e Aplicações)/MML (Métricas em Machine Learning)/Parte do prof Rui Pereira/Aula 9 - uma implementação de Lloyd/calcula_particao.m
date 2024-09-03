function P=calcula_particao(Mx,My,x,K)
N=length(x); %N numero de elementos da BD

% Para todos os eventos calcula dissemelhanca entre evento e
% representantes. Atribui classe daquele que é menos dissemelhante.

for i=1:N % para todos os eventos
  for j=1:K % para todas os clusters
   %d(i,j) tem a distancia do evento i ao representate j   
   d(i,j)=calcula_dissemelhanca(Mx(j),My(j),x(i,:)); %x(i,:) corresponte a 1 array com 2 coordenadas de x do evento i
  end
end
d

P=constroi_particao(d,N,K); %P contem lista de indices dos representantes para cada evento da BD
end