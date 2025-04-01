function boyer_moore_majority(votes: number[]): number | undefined {
  let candidate = votes[0];
  let count = 1;
  const len = votes.length;

  for (let i = 2; i < len; i++) {
    if (count === 0) {
      candidate = votes[i];
    }
    if (votes[i] === candidate) {
      count++;
    } else {
      count--;
    }
  }

  let candidateVotes = 0;
  for (let i = 0; i < len; i++) {
    if (votes[i] === candidate) {
      candidateVotes++;
      if (candidateVotes > len / 2) {
        return candidate;
      }
    }
  }
  return undefined;
}

const candidate = boyer_moore_majority([3, 3, 4, 2, 4, 3, 3, 2, 3, 3]);
console.log(`candidate`, candidate);