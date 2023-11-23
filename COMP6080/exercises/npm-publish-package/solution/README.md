## Publish an NPM package

Publishing an `npm` package

`npm` is the default package manager for `node.js`, and it has a command line interface that allows a user to easily build all the required libraries for a particular JavaScript (or TypeScript!) project.

To publish an `npm` package, you must first ensure that `node` and `npm` are installed on your system. Then, you must create an `npm` account [here](https://www.npmjs.com/signup).

Afterwards, login through your terminal with 
```sh
npm login
```
and enter all the required details.

___

Create a new folder, which will contain the files that will consist your package. Let's name it `webfeprog-publish-` + today's date. Afterwards, navigate to the newly created folder.

e.g.
```sh
mkdir webfeprog-publish-20jan
cd webfeprog-publish-20jan
```

___

`npm` has certain commands that make it really easy for us to create and publish `npm` packages.

In your terminal, type:
```sh
npm init
```

Afterwards, go through all the prompts as appropriate. This will create a `package.json` file in the root directory of your package.

This `package.json` file will contain all the relevant metadata for your project. You are able to edit these manually through your IDE!

What information do the following fields hold?

- `version`
  > A field that contains the version of the package that you are currently working with.

- `main`
  > A string that describes the path to the primary entry point to your program, and is defaulted to `index.js`. This is where all your package exports should go, to make things easier for whoever uses your package. 

  > For example, if you have a default exported `add` function in `webfeprog-publish-ddMMM/util/add.js`, and that is also exported in `webfeprog-publish-ddMMM/index.js`, a user can import it from your package using the first line rather than the second.
  > ```js
  > import { add } from "webfeprog-publish-ddMMM";
  > 
  > import add from "webfeprog-publish-ddMMM/util/add.js";
  > ```

- `scripts`
  > A dictionary containing script commands. The key is the `script`, and the value is the script command, and they are run using `npm <script>`. These scripts are run during preset life cycle events (Such as `prepare`), or are default scripts (Such as `start` or `install`), or are arbitrary user-made scripts (Such as `test`).

- `dependencies`
  > A dictionary that maps a package name to a version range. These packages generally are required for your package to work! You do not need to manually add dependencies, you can do it through this terminal command, when in your project root directory:
  > ```sh
  > npm install <package_name> --save
  > ```

- `repository`
  > An object with at least `type` and `url` fields, which contain where the code for you package will live.

- `author` and `contributors`
  > An object, and an array of objects, respectively. These objects describe the details of the people behind the package, and at the minimum should contain a `name` field, and at most, should contain `name`, `email` and `url` fields.

___

Let's create an `index.js` file in the root directory for your package, and let's just make it print `Hello world!` to the console.

Now, let's adjust `package.json`. Change the `version` field to `"version": "0.0.1"`, and add yourself to the `author` field.

> ```js
> {
>   ...
>   "author": {
>     "name": "Clarence"
>   },
> }
> ```

Finally, let's add a script to the `scripts` field that would run our `index.js`.

> ```js
> {
>   ...
>   "script": {
>     ...
>     "start": "node index.js",
>   },
> }
> ```

Check that it works by running `npm start` in your terminal. It should just say `Hello world!` in your terminal!

___

After all that it's time to publish. To do that, all you need to run is 

```sh
npm publish
```

Seeing your package name and version at the end of `npm publish` means that it worked! For example, I would see 
```sh
+ webfeprog-publish-20jan@0.0.1
```
and I can find the package at [this link](https://www.npmjs.com/package/webfeprog-publish-20jan) afterwards.