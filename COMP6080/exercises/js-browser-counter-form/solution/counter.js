const counter = document.getElementById("counter");

// 2. Populate counter with a 0
counter.innerText = "0";

// 3. Increment by 1 when the '+' button is clicked
const increment = document.getElementById("increment");
increment.addEventListener("click", () => {
  const curCount = parseInt(counter.innerText);

  // 5. Check upper bound of counter
  if (curCount >= 10) {
    alert("Can't count past 10!");
  } else {
    counter.innerText = curCount + 1;
  }
});

// 4. Decrement by 1 when the '-' button is clicked
const decrement = document.getElementById("decrement");
decrement.addEventListener("click", () => {
  const curCount = parseInt(counter.innerText);

  // 5. Check lower bound of counter
  if (curCount <= 0) {
    alert("Can't count below 0!");
  } else {
    counter.innerText = curCount - 1;
  }
});
