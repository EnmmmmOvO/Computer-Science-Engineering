const question1 = () => {
  const microsoft = getCompanyRepos("microsoft");
  const google = getCompanyRepos("google");
  const canva = getCompanyRepos("canva");

  Promise.all([microsoft, google, canva])
      .then(list => list.forEach(company => company.forEach((repo) => console.log(repo))))
}

const question2 = async () => {
  const microsoft = getCompanyRepos("microsoft");
  const google = getCompanyRepos("google");
  const canva = getCompanyRepos("canva");

  try {
    const promise = await Promise.all([microsoft, google, canva])
    promise.forEach(company => company.forEach((repo) => console.log(repo)))
  } catch (e) {
    console.error(e);
  }
}

const question3 = async () => {
  const microsoft = getCompanyRepos("microsoft");
  const fake = getCompanyRepos("fake");

  try {
    const promise = await Promise.all([microsoft, fake])
    promise.forEach(company => company.forEach((repo) => console.log(repo)))
  } catch (e) {
    console.error(e);
  }
}

const question4 = async () => {
  const microsoft = getCompanyRepos("microsoft");
  const fake = getCompanyRepos("fake");
  const google = getCompanyRepos("google");
  const canva = getCompanyRepos("canva");

  try {
    const promise = await Promise.allSettled([microsoft, fake, google, canva])
    promise.forEach(company => {
      if (company.status === 'fulfilled') company.value.forEach((repo) => console.log(repo))
    });
  } catch (e) {
    console.error(e);
  }
}

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
