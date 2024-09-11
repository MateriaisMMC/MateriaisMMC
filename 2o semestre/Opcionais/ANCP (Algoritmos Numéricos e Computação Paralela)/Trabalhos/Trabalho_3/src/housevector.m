function [v, beta] = housevector(x)
    n = length(x);
    sig = x(2:n)' * x(2:n);
    v = x;
    if (sig ~= 0)
        mu = sqrt(x(1)^2 + sig);
        if (x(1) <= 0)
            v(1) = x(1) - mu;
        else
            v(1) = -sig / (x(1) + mu);
        end
    end
    v = v / sqrt(v' * v);
    beta = sig;