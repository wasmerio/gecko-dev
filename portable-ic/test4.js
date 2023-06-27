let sum = 0;
let o = { k: 1 };
for (let i = 0; i < 10*1000*1000; i++) {
    sum = o.k - sum;
}
print(sum);
