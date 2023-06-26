let sum = 0;
for (let i = 0; i < 100*1000*1000; i++) {
    sum = 1 - sum;
}
print(sum);
