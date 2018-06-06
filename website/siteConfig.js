/**
 * Copyright (c) 2017-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

// See https://docusaurus.io/docs/site-config.html for all the possible
// site configuration options.

/* List of projects/orgs using your project for the users page */
const users = [
  {
    caption: 'Clause Inc.',
    // You will need to prepend the image path with your baseUrl
    // if it is not '/', like: '/test-site/img/ergologo.svg'.
    image: 'img/clause-logo-sm.jpg',
    infoLink: 'http://clause.io',
    pinned: true,
  },
];

const siteConfig = {
  title: 'Ergo' /* title for your website */,
  tagline: 'The Accord Project language for smart legal contracts. Ergo lets you write safe and portable logic for your legal clause and contract templates.',
  url: 'https://ergo.accordproject.org' /* your website url */,
  cname: 'ergo.accordproject.org' /* CNAME */,
  baseUrl: '/' /* base url for your project */,
  // For github.io type URLs, you would set the url and baseUrl like:
  //   url: 'https://facebook.github.io',
  //   baseUrl: '/test-site/',

  // Used for publishing and more
  projectName: 'ergo',
  organizationName: 'accordproject',
  // For top-level user or org sites, the organization is still the same.
  // e.g., for the https://JoelMarcey.github.io site, it would be set like...
  //   organizationName: 'JoelMarcey'

  // For no header links in the top nav bar -> headerLinks: [],
  headerLinks: [
    {doc: 'ergo-overview', label: 'Docs'},
    { href: "https://accordproject.github.io/ergo-playground", label: "Try" },
    { search: true },
    { href: "https://docs.accordproject.org", label: "Accord" },
    { href: "https://github.com/accordproject/ergo", label: "GitHub" },
  ],

  // If you have users set above, you add it here:
  users,

  /* path to images for header/footer */
  headerIcon: 'img/ergologo.svg',
  footerIcon: 'img/ergologo.svg',
  favicon: 'img/favicon.png',

  /* colors for website */
  colors: {
    primaryColor: '#008B8B',
    secondaryColor: '#008B8B',
  },

  /* custom fonts for website */
  /*fonts: {
    myFont: [
      "Times New Roman",
      "Serif"
    ],
    myOtherFont: [
      "-apple-system",
      "system-ui"
    ]
  },*/

  // This copyright info is used in /core/Footer.js and blog rss/atom feeds.
  copyright:
    'Copyright © ' +
    new Date().getFullYear() +
    ' Clause Inc.',

  highlight: {
    // Highlight.js theme to use for syntax highlighting in code blocks
    theme: 'default',
  },

  // Add custom scripts here that would be placed in <script> tags
  scripts: ['https://buttons.github.io/buttons.js'],

  /* On page navigation for the current documentation page */
  onPageNav: 'separate',

  /* Open Graph and Twitter card images */
  ogImage: 'ergologo.png',
  twitterImage: 'ergologo.png',

  // You may provide arbitrary config keys to be used as needed by your
  // template. For example, if you need your repo's URL...
  repoUrl: 'https://github.com/accordproject/ergo',
};

module.exports = siteConfig;
