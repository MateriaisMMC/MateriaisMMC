function [evento, termina, dir] = myeventos(~,y)
evento = y(1)-0.75; %  y(1)-0.75=0
termina = 0; % continua (1 termina) após encontrar x tal que y(x)=0.75;
dir = []; %  se a função  que define o evento está a crescer 
             %(dir=1) ou a decrescer  (dir=-1)quando atinge o valor;
end