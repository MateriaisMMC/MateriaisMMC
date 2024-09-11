function questao_2
    % Load Image
    A = imread('street1.jpg');
    A = rgb2gray(A);
    imshow(A)
    title(['Original (', sprintf('Rank %d)', rank(double(A)))])
    pause

    % Compress Image a first time
    [U1, S1, V1] = svdsketch(double(A), 1e-2);
    Anew1 = uint8(U1 * S1 * V1');
    imshow(uint8(Anew1))
    title(sprintf('Rank %d approximation', size(S1, 1)))
    pause
    
    % Compress Image a second time
    [U2, S2, V2] = svdsketch(double(A), 1e-1);
    Anew2 = uint8(U2 * S2 * V2');
    imshow(Anew2)
    title(sprintf('Rank %d approximation', size(S2, 1)))
    pause

    % Compress Image a third time
    [U3, S3, V3, apxErr] = svdsketch(double(A), 1e-1, 'MaxSubspaceDimension', 15);
    Anew3 = uint8(U3 * S3 * V3');
    imshow(Anew3)
    title(sprintf('Rank %d approximation', size(S3, 1)))
end