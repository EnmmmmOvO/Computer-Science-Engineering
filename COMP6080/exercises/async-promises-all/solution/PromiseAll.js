/**
 * In this exercise, we will be looking at `Promise.all`.
 * `Promise.all` allows you to aggregate/analyse the results of multiple asynchronous calls at once.
 * You can give it an array of promises and once resolved, it will return an array of results to you.
 * For more information, see the [MDN docs](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Promise/all).
 *
 * The file `PromiseAll.js` contains a function called `getCompanyRepos`. It fetches a given company's public repositories from GitHub.
 * If the company does not exist or has no information available, it will throw an error.
 *
 * We will be using NPM + Node.js for this exercise. When you go into the exercise folder, run `npm install`.
 * To run the exercise, execute `node PromiseAll.js`.
 */

/**
 * Fetches public repo information from GitHub for a specific company
 * @param {String} companyName Company name
 * @returns A list of repo names belonging to the company
 */
async function getCompanyRepos(companyName) {
  // Since fetch isn't in NodeJS, use a library to polyfill it
  const fetch = require("node-fetch");

  // Fetch the company's repos from GitHub
  const response = await fetch(
    `https://api.github.com/orgs/${companyName}/repos`
  );
  const data = await response.json();

  // If the response is not OK, throw an error
  // This is the same as Promise.reject() in non-async functions
  if (response.status !== 200) {
    throw new Error(`Response of ${response.status} for ${companyName}`);
  }

  // Push the full names of each repo into an array
  const repoArray = [];
  data.forEach((repo) => repoArray.push(repo.full_name));

  return repoArray;
}

/**
 * Currently, the `question1` function gets the repo names of "microsoft", "google" and "canva" and prints them out as soon each promise resolves.
 * Using `Promise.all` and `.then`, modify `question1()` so that the repo names are printed out all at once.
 *
 * HINT: you can store an unresolved Promise in a variable like this: `const microsoftRepos = getCompanyRepos("microsoft");`
 */
function question1() {
  const microsoftRepos = getCompanyRepos("microsoft");
  const googleRepos = getCompanyRepos("google");
  const canvaRepos = getCompanyRepos("canva");

  Promise.all([microsoftRepos, googleRepos, canvaRepos]).then((companies) => {
    companies.forEach((company) => {
      company.forEach((repo) => console.log(repo));
    });
  });
}

/**
 * Repeat question 1, but use `async` and `await` instead.
 */
async function question2() {
  const microsoftRepos = getCompanyRepos("microsoft");
  const googleRepos = getCompanyRepos("google");
  const canvaRepos = getCompanyRepos("canva");

  try {
    const companies = await Promise.all([
      microsoftRepos,
      googleRepos,
      canvaRepos,
    ]);

    companies.forEach((company) => {
      company.forEach((repo) => console.log(repo));
    });
  } catch (error) {
    console.log(error);
  }
}

/**
 * See what happens when you give `Promise.all` a `Promise` that will reject.
 * Do this by getting the repo names of "microsoft" as well as "some_fake_company".
 * Does `Promise.all` resolve or reject?
 * Are we able to see the repo names of "microsoft"?
 */
async function question3() {
  const microsoftRepos = getCompanyRepos("microsoft");
  const fakeRepos = getCompanyRepos("some_fake_company");

  try {
    // Promise.all will reject here because fakeRepos rejects
    const companies = await Promise.all([microsoftRepos, fakeRepos]);

    // Will not get to here, so we don't see Microsoft's repo names
    companies.forEach((company) => {
      company.forEach((repo) => console.log(repo));
    });
  } catch (error) {
    console.log(error);
  }
}

/**
 * If you don't need the results of promise that was rejected, you can use `Promise.allSettled` instead of `Promise.all`.
 * Instead of an array of resolved results, `Promise.allSettled` returns an array of fulfilled or rejected items.
 * Each item will have one of the two formats:
 *
 * 1. `{ status: "fulfilled", value: ... }`
 * 2. `{ status: "rejected", reason: ... }`
 *
 * Use `Promise.allSettled` to print the repo names of "microsoft", "google", "canva" and "some_fake_company".
 * If you encounter a `status === "rejected"` item, log the reason for it rejecting.
 */
async function question4() {
  const microsoftRepos = getCompanyRepos("microsoft");
  const googleRepos = getCompanyRepos("google");
  const canvaRepos = getCompanyRepos("canva");
  const fakeRepos = getCompanyRepos("some_fake_company");

  try {
    // Promise.allSettled will not reject here
    const results = await Promise.allSettled([
      microsoftRepos,
      googleRepos,
      canvaRepos,
      fakeRepos,
    ]);

    // result will be either { status: "fulfilled", value: ... } or { status: "rejected", reason: ... }
    results.forEach(({ status, ...result }) => {
      if (status === "fulfilled") {
        result.value.forEach((repo) => console.log(repo));
      } else {
        // Do whatever error handling you want - we just log the reason (as opposed to throwing it)
        console.log(result.reason);
      }
    });
  } catch (error) {
    console.log(error);
  }
}
