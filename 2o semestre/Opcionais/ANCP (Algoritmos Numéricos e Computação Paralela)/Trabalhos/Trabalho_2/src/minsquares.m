function minsquares()
    % Define x and y vectors
    x = [0 2 3 5 8 11 12 15]';
    y = [50; 56; 60; 72; 85; 100; 110; 125];
    disp('x:');
    disp(x);
    disp(' ');  % Add a space for better readability
    disp('y:');
    disp(y);
    
    % Figura 1
    minsquares_line(x, y)

    % Figura 2
    minsquares_parabola(x, y)
end

function minsquares_line(x, y)
    % Create matrix A
    A = [ones(length(x), 1), x];
    
    % Print results
    disp('A:');
    disp(A);

    alpha = (inv(A' * A) * A') * y;
    
    % Print alpha
    disp('alpha:');
    disp(alpha);
    
    figure;
    plot(x, y, 'b.', 'markersize', 12, 'DisplayName', 'Data Points');
    hold on;
    plot(x, alpha(1) + alpha(2) * x);
    hold off;
    xlabel('x');
    ylabel('y');
    title('Least Squares Fit (Line)');
    grid on;
    legend();
end

function minsquares_parabola(x, y)
    A = [ones(length(x), 1), x, x.^2];
    disp('A:');
    disp(A);

    alpha = (inv(A' * A) * A') * y;
    disp('alpha:');
    disp(alpha);
    
    figure;
    plot(x, y, 'b.', 'markersize', 12, 'DisplayName', 'Data Points');
    hold on;
    plot(x, alpha(1) + alpha(2) * x + alpha(3) * x.^2);
    hold off;
    xlabel('x');
    ylabel('y');
    title('Least Squares Fit (Line)');
    grid on;
    legend();
end